import socket
import ipaddress
import sys
import threading
import math
import dpkt
import time
import binascii
import numpy as np
import os
import netifaces as ni
import csv
from datetime import datetime

from dpkt.utils import inet_to_str, mac_to_str

from PyQt5.QtWidgets import QBoxLayout, QComboBox, QFileDialog, QGroupBox, QPushButton, QSizePolicy, QSpacerItem, QTableWidget, QApplication, QVBoxLayout, QTableWidgetItem, QDialog, QLabel
from PyQt5.QtWidgets import QGridLayout, QHBoxLayout, QCheckBox, QHeaderView
from PyQt5.QtCore import QPointF, QTimer, Qt, QSortFilterProxyModel
from PyQt5.QtGui import QColor, QPainter, QPixmap
from PyQt5.QtChart import QChart, QSplineSeries, QChartView, QValueAxis
from pyqtgraph import PlotWidget, AxisItem

BASH_PATH = os.path.dirname(os.path.realpath(__file__))

def check_in_network(ip, net):
    return ipaddress.ip_address(ip) in ipaddress.ip_network(net)

def get_network_address(ip, netmask):
    return ipaddress.ip_network('{}/{}'.format(ip, netmask), strict=False)

def convert_size(size_bytes):
        if size_bytes <= 0:
            return "0B"

        size_name = ("B", "KB", "MB", "GB", "TB", "PB", "EB", "ZB", "YB")
        i = int(math.floor(math.log(size_bytes, 1024)))
        p = math.pow(1024, i)
        s = round(size_bytes / p, 2)
        return "%s %s" % (s, size_name[i])

def get_interfaces():
    iface_ids = ni.interfaces()
    ifaces = []
    for id in iface_ids:
        addrs = ni.ifaddresses(id)
        iface = {
            'name': id,
            'mac': addrs[ni.AF_LINK][0]['addr'],
            'ip': '',
            'network': '',
            'ip6': '',
            'network6': ''
        }
        
        if ni.AF_INET in addrs:
            iface['ip'] = addrs[ni.AF_INET][0]['addr']
            iface['network'] = get_network_address(addrs[ni.AF_INET][0]['addr'], addrs[ni.AF_INET][0]['netmask'])

        if ni.AF_INET6 in addrs and addrs[ni.AF_INET6][0]['addr']:

            iface['ip6'] = addrs[ni.AF_INET6][0]['addr']
            if iface['ip6'].endswith('%'+id):
                iface['ip6'] = iface['ip6'].replace('%'+id, '')

            netmask6 = bin(int(ipaddress.IPv6Address(addrs[ni.AF_INET6][0]['netmask']))).count('1')

            iface['network6'] = get_network_address(iface['ip6'], netmask6)

        ifaces.append(iface)
    
    return ifaces


class NumberSortModel(QSortFilterProxyModel):
    def lessThan(self, left, right):
        lvalue = left.data().toDouble()[0]
        rvalue = right.data().toDouble()[0]
        return lvalue < rvalue

class SpeedAxisItem(AxisItem):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # self.setLabel(text='Speed', units=None)
        self.enableAutoSIPrefix(False)

    def tickStrings(self, values, scale, spacing):
        return [convert_size(value) for value in values]

class App(QDialog):
    def __init__(self):
        super().__init__()
        self.title = 'Localnet Monitor'
        self.left = 0
        self.top = 0
        self.width = 800
        self.height = 800
        self.refresh_rate = 1000 # 1 detik
        self.is_capture = False
        self.log_traffic_file = '/tmp/localnet-traffic.log'
        self.log_mac_ip_file = '/tmp/localnet-mac_ip.log'
        self.save_folder = None
        self.is_autosave = False
        self.is_router = True
        self.save_log_rate = 30 * 1000 # 30 detik
        self.data_header = [
            'time', 
            'src_mac_id', 
            'dst_mac_id',
            'type',
            'src_port',
            'dst_port',
            'length'
        ]

        self.interfaces = get_interfaces()
        self.iface = self.interfaces[0]

        self.my_key = ''
        self.is_calculate = False 

        try:
            self.conn = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.ntohs(3))
            self.conn.close()
        except PermissionError as e: 
            print(e)
            exit()

        self._init_data()
        self._init_gui()

    def get_domain(self, ip):
        self.check_domain_cache(ip)
        return self.domain_cache[ip]

    def check_domain_cache(self, ip):
        if ip not in self.domain_cache:
            self.domain_cache[ip] = {
                'name': [],
                'visited': 0,
                'data_usage': 0
            }
    
    def is_same_network(self, ip):
        in_network = False
        if self.iface['network'] != '':
            in_network = in_network or check_in_network(ip, self.iface['network'])
        
        if self.iface['network6'] != '': 
            in_network = in_network or check_in_network(ip, self.iface['network6'])
        
        return in_network

    def get_item(self, key):
        self.check_item(key)
        index = self.key_map[key]
        return self.data[index]

    def onchecked_router(self):
        self.is_router = self.is_router_checkbox.isChecked()

    def check_item(self, key, ip='', ip6='', hostname=''):
        if key not in self.key_map:
            self.key_map[key] = len(self.data)
            self.data.append({
                'mac': key,
                'ip': ip,
                'ip6': ip6,
                'host_name': hostname,
                'tx_length': 0,
                'rx_length': 0,
                'tx_gap': 0,
                'rx_gap': 0
            })

    def _init_data(self):
        self.buffers = []
        self.traffic_records = []
        self.domain_cache = {}
        self.data = []
        self.my_data = []
        self.key_map = {}
        self.key_mac_ip = {}
        self.data_temp = []

        self.total_tx = 0
        self.total_rx = 0

        self.tx_speed_data = np.array([0])
        self.rx_speed_data = np.array([0])
        self.curr_max_speed = 1

        if not self.is_router:
            self.check_item(self.iface['mac'], self.iface['ip'], self.iface['ip6'])
        
        # log data
        self.log_timer = QTimer(self)
        self.log_timer.timeout.connect(self.save_log_data)
    
    def _init_log_file(self):
        # log data
        with open(self.log_traffic_file, 'w', encoding='UTF8', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(self.data_header)

    def _init_network_monitor(self):
        self.conn = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.ntohs(3))
        self.th_capture = threading.Thread(target=self.network_monitor)
        self.th_capture.daemon = True
        self.th_capture.start()

    def _init_counter(self):
        self.th_counter = threading.Thread(target=self.count_traffic)
        self.th_counter.daemon = True
        self.th_counter.start()

    def _init_gui(self):
        self.setWindowTitle(self.title)
        self.resize(self.width, self.height)

        self._create_table()
        self._create_domain_table()
        self._create_combobox_interface()

        self.image_tx = QLabel(self) 
        self.image_rx = QLabel(self)
        self.image_tx.setPixmap(QPixmap(BASH_PATH + '/arrow-up.png'))
        self.image_rx.setPixmap(QPixmap(BASH_PATH + '/arrow-down.png'))
        self.image_tx.setFixedSize(50, 50)
        self.image_rx.setFixedSize(50, 50)
        self.image_tx.setScaledContents(True)
        self.image_rx.setScaledContents(True)

        self.labelTxTotal = QLabel('Total Data: 0 B')
        self.labelTxSpeed = QLabel('Speed: 0 B/s')
        self.labelRxTotal = QLabel('Total Data: 0 B')
        self.labelRxSpeed = QLabel('Speed: 0 B/s')

        sendingGroup = QGroupBox("Sending")
        sendingLayout = QHBoxLayout()
        sendingLayout.addWidget(self.image_tx, 1, alignment=Qt.AlignCenter)

        sendingLabelLayout = QVBoxLayout()
        sendingLabelLayout.addItem(QSpacerItem(0, 10, QSizePolicy.Minimum, QSizePolicy.Expanding))
        sendingLabelLayout.addWidget(self.labelTxSpeed)
        sendingLabelLayout.addWidget(self.labelTxTotal)
        sendingLabelLayout.addItem(QSpacerItem(0, 10, QSizePolicy.Minimum, QSizePolicy.Expanding))

        sendingLayout.addLayout(sendingLabelLayout, 2)

        sendingGroup.setLayout(sendingLayout)

        receiveGroup = QGroupBox("Receive")
        receiveLayout = QHBoxLayout()
        receiveLayout.addWidget(self.image_rx, 1, alignment=Qt.AlignCenter)

        receiveLabelLayout = QVBoxLayout()
        receiveLabelLayout.addItem(QSpacerItem(0, 10, QSizePolicy.Minimum, QSizePolicy.Expanding))
        receiveLabelLayout.addWidget(self.labelRxSpeed)
        receiveLabelLayout.addWidget(self.labelRxTotal)
        receiveLabelLayout.addItem(QSpacerItem(0, 10, QSizePolicy.Minimum, QSizePolicy.Expanding))

        receiveLayout.addLayout(receiveLabelLayout, 2)

        receiveGroup.setLayout(receiveLayout)

        self.is_router_checkbox = QCheckBox("A Router")
        self.is_router_checkbox.setChecked(self.is_router)
        self.is_router_checkbox.stateChanged.connect(self.onchecked_router)

        self.autoSaveCheckBox = QCheckBox("Auto save")
        if self.save_folder == None:
            self.autoSaveCheckBox.setEnabled(False)

        self.chart = QChart()
        self.rx_series = QSplineSeries(color=QColor('#0000FF'))
        self.tx_series = QSplineSeries(color=QColor('#FF0000'))
        self.chart.addSeries(self.rx_series)
        self.chart.addSeries(self.tx_series)
        self.chart_view = QChartView(self.chart)        
        self.chart_view.setFixedHeight(150)

        self.axis_x = QValueAxis(min=0, max=60, tickCount=7, labelFormat='%.g', reverse=True)
        self.axis_y = QValueAxis(tickCount=5)

        self.chart.addAxis(self.axis_x, Qt.AlignBottom)
        self.chart.addAxis(self.axis_y, Qt.AlignRight)
        
        self.chart.legend().hide()
        self.chart.setContentsMargins(-15, -15, -15, -15)
        self.chart.layout().setContentsMargins(0, 0, 0, 0)
        self.chart.setBackgroundRoundness(0)
        self.chart_view.setRenderHint(QPainter.Antialiasing)

        self.rx_series.attachAxis(self.axis_x)
        self.rx_series.attachAxis(self.axis_y)
        self.tx_series.attachAxis(self.axis_x)
        self.tx_series.attachAxis(self.axis_y)

        topLayout = QHBoxLayout()
        self.capture_button = QPushButton('Capture')
        self.capture_button.clicked.connect(self.toggle_capture)
        topLayout.addWidget(self.interface_combobox)
        self.directory_button = QPushButton('Folder...')
        self.directory_button.clicked.connect(self.open_folder)
        topLayout.addWidget(self.directory_button)
        topLayout.addWidget(self.autoSaveCheckBox)
        topLayout.addWidget(self.capture_button)
        topLayout.addItem(QSpacerItem(10, 0, QSizePolicy.Expanding, QSizePolicy.Minimum))
        topLayout.addWidget(self.is_router_checkbox)

        topDomainGroup = QGroupBox('Top Domain')
        topDomainlayout = QVBoxLayout()
        topDomainlayout.addWidget(self.table_domain)
        topDomainGroup.setLayout(topDomainlayout)

        clientTrafficGroup = QGroupBox('Client Traffic')
        clientTrafficLayout = QVBoxLayout()
        clientTrafficLayout.addWidget(self.table_widget)
        clientTrafficGroup.setLayout(clientTrafficLayout)

        totalLayout = QHBoxLayout()
        totalLayout.addWidget(sendingGroup, 1)
        totalLayout.addWidget(receiveGroup, 1)
        
        trafficLayout = QVBoxLayout()
        trafficLayout.addLayout(totalLayout)
        trafficLayout.addWidget(self.chart_view)
        trafficLayout.addWidget(clientTrafficGroup, 2)
        trafficLayout.addWidget(topDomainGroup, 2)

        mainLayout = QGridLayout()
        mainLayout.addLayout(topLayout, 0, 0, 1, 2)
        mainLayout.addLayout(trafficLayout, 1, 0)

        self.setLayout(mainLayout) 

        # Show widget
        self.show()
    
    def _update_bandwidth_chart(self, new_tx, new_rx):
        if self.rx_series.count() > 60:
            self.rx_series.remove(60)
            self.tx_series.remove(60)

        max_speed = 0
        for i in range(self.rx_series.count()):
            old_rx = self.rx_series.at(i)
            old_rx.setX(i + 1)
            old_tx = self.tx_series.at(i)
            old_tx.setX(i + 1)
            self.rx_series.replace(i, old_rx)
            self.tx_series.replace(i, old_tx)

            max_speed = math.ceil(np.max([old_rx.y(), old_tx.y(), max_speed]))
        
        max_value = np.max([max_speed, new_tx, new_rx])
        self.axis_y.setMax(max_value)
        
        self.rx_series.insert(0, QPointF(0, new_rx))
        self.tx_series.insert(0, QPointF(0, new_tx))

    def _create_combobox_interface(self):
        self.interface_combobox = QComboBox()
        for iface in self.interfaces:
            if iface['name'] == 'lo':
                continue
            
            self.interface_combobox.addItem(iface['name'], iface)

    def _create_table(self):
        # Create table
        column = ['MAC', 'IP', 'Host Name', 'TX', 'RX', 'TX Speed', 'RX Speed']
        self.table_widget = QTableWidget()
        self.table_widget.setColumnCount(len(column))

        self.table_widget.setHorizontalHeaderLabels(column)
        header = self.table_widget.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(1, QHeaderView.ResizeToContents)
        header.setSectionResizeMode(2, QHeaderView.Stretch)

        self.table_timer = QTimer(self)
        self.table_timer.timeout.connect(self._update_table)
    
    def _create_domain_table(self):
        column = ['Site', 'Usage']
        self.table_domain = QTableWidget()
        self.table_domain.setColumnCount(len(column))

        self.table_domain.setHorizontalHeaderLabels(column)
        header = self.table_domain.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.Stretch)
    
    def get_mac_ip_key(self, mac, ip=''):
        key = '{}-{}'.format(mac, ip)
        if mac not in self.key_mac_ip:
            self.key_mac_ip[key] = {
                'id': len(self.key_mac_ip),
                'ip': ip,
                'mac': mac
            }
        
        return self.key_mac_ip[key]

    def save_log_data(self):
        data = self.data_temp.copy()
        self.data_temp = []

        with open(self.log_traffic_file, 'a', encoding='UTF8', newline='') as f:
            writer = csv.writer(f)
            writer.writerows(data)
        
        with open(self.log_mac_ip_file, 'w', encoding='UTF8', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['id', 'mac', 'ip', 'domain'])
            for key, value in self.key_mac_ip.items():
                if value['ip'] in self.domain_cache:
                    domain = ','.join(self.domain_cache[value['ip']]['name'])
                else:
                    domain = ''
                writer.writerow([value['id'], value['mac'], value['ip'], domain])
    
    def open_folder(self):
        folder = QFileDialog.getExistingDirectory(None, 'Select a Folder', '', QFileDialog.ShowDirsOnly)
        self.save_folder = folder
        
        if folder == '':
            self.save_folder = None

        if self.save_folder != None:
            self.autoSaveCheckBox.setEnabled(True)
            print('selected folder:', self.save_folder)

    def toggle_capture(self):
        self.is_capture = not self.is_capture
        self.iface = self.interface_combobox.currentData()
        self.my_key = self.iface['mac']

        if self.is_capture == True:
            self._init_data()
            self.interface_combobox.setEnabled(False)
            self.capture_button.setText('Stop')
            self.start_capture()
        else:
            self.capture_button.setText('Capture')
            self.interface_combobox.setEnabled(True)
            self.stop_capture()


    def filter_me(self, data):
        my_data = self.my_data_usage()
        index = self.key_map[self.my_key]
        data[index] = my_data

        return data
    
    def _update_total_traffic(self, new_tx, new_rx):
        self.total_tx += new_tx
        self.total_rx += new_rx

        self.labelTxTotal.setText('Total Data: {}'.format(convert_size(self.total_tx)))
        self.labelTxSpeed.setText('{}'.format(convert_size(new_tx) + '/s'))
        self.labelRxTotal.setText('Total Data: {}'.format(convert_size(self.total_rx)))
        self.labelRxSpeed.setText('{}'.format(convert_size(new_rx) + '/s'))

    def _render_table_row(self):
        self.is_calculate = True
        self.table_widget.setRowCount(0)

        sorted_data = self.data.copy()
        sorted_data = sorted(sorted_data, key = lambda i: (i['rx_length'], i['tx_length']), reverse=True)

        total_tx = 0
        total_rx = 0
        for index, item in enumerate(sorted_data):
            row = self.table_widget.rowCount()

            self.table_widget.insertRow(row)

            mac = item['mac']
            ip = item['ip']
            host_name = item['host_name']
            tx = convert_size(item['tx_length'])
            rx = convert_size(item['rx_length'])
            sp_tx = convert_size(item['tx_gap']) + '/s'
            sp_rx = convert_size(item['rx_gap']) + '/s'

            total_tx += item['tx_gap']
            total_rx += item['rx_gap']
            
            self.data[index]['tx_gap'] = 0
            self.data[index]['rx_gap'] = 0

            self.table_widget.setItem(row, 0, QTableWidgetItem(mac))
            self.table_widget.setItem(row, 1, QTableWidgetItem(ip))
            self.table_widget.setItem(row, 2, QTableWidgetItem(host_name))
            self.table_widget.setItem(row, 3, QTableWidgetItem(tx))
            self.table_widget.setItem(row, 4, QTableWidgetItem(rx))
            self.table_widget.setItem(row, 5, QTableWidgetItem(sp_tx))
            self.table_widget.setItem(row, 6, QTableWidgetItem(sp_rx))
        
        self.is_calculate = False

        self._update_bandwidth_chart(total_tx, total_rx)
        self._update_total_traffic(total_tx, total_rx)

    def _render_domain_table(self):
        domain_sorted = sorted(self.domain_cache.items(), key=lambda i: i[1]['data_usage'], reverse=True)
        domain_sorted = domain_sorted[:30]

        self.table_domain.setRowCount(0)

        for index, item in enumerate(domain_sorted):
            row = self.table_domain.rowCount()
            self.table_domain.insertRow(row)
            
            if len(item[1]['name']) > 0:
                name = ','.join(item[1]['name'])
            else:
                name = item[0]

            usage = convert_size(item[1]['data_usage'])

            self.table_domain.setItem(row, 0, QTableWidgetItem(name))
            self.table_domain.setItem(row, 1, QTableWidgetItem(usage))

    def _update_table(self): 
        self._render_table_row()
        self._render_domain_table()
     
    
    def my_data_usage(self):
        curr = self.get_item(self.my_key).copy()
        
        other_usage = [[i['tx_length'], i['rx_length'], i['tx_gap'], i['rx_gap']] for i in self.data if i['mac'] is not curr['mac']]
        
        otx_length, orx_length, otx_gap, orx_gap = (0, 0, 0, 0)

        for i in other_usage:
            otx_length += i[0]
            orx_length += i[1]
            otx_gap += i[2]
            orx_gap += i[3]
        
        curr['tx_length'] -= otx_length
        curr['rx_length'] -= orx_length
        curr['tx_gap'] -= otx_gap
        curr['rx_gap'] -= orx_gap

        return curr

    def start_capture(self):
        self._init_network_monitor()
        self._init_counter()
        
        self.table_timer.start(self.refresh_rate)

        self.autoSaveCheckBox.setEnabled(False)
        self.directory_button.setEnabled(False)
        self.is_router_checkbox.setEnabled(False)
        
        if self.save_folder != None and self.autoSaveCheckBox.isChecked():
            default_name = 'localnet-' + time.strftime("%Y-%m-%d-%H-%M-%S")
            self.log_traffic_file = os.path.join(self.save_folder, default_name + '_traffic-data.csv')
            self.log_mac_ip_file = os.path.join(self.save_folder,default_name + '_mac_ip-data.csv')

            self._init_log_file()
            self.log_timer.start(self.save_log_rate)

    def stop_capture(self):
        self.directory_button.setEnabled(True)
        self.is_router_checkbox.setEnabled(True)

        if self.save_folder != None:
            self.autoSaveCheckBox.setEnabled(True)
        
        self.table_timer.stop()
        self.log_timer.stop()

    def network_monitor(self):
        while self.is_capture:
            raw_data, addr = self.conn.recvfrom(65536)

            if addr[0] == self.iface['name'] or addr[0] == 'lo':
                now = int(datetime.utcnow().timestamp())
                self.buffers.append([now, raw_data])
        
        self.conn.close()


    def count_traffic(self):
        while self.is_capture:
            if len(self.buffers) == 0 or self.is_calculate:
                time.sleep(0.1)
                continue

            timestamp, raw_data = self.buffers.pop(-(len(self.buffers)))

            packet_length = len(raw_data)

            # mengambil ethernet header dari paket
            eth = dpkt.ethernet.Ethernet(raw_data)
            src_mac = mac_to_str(eth.src)
            dst_mac = mac_to_str(eth.dst)

            # memastikan paket IP

            if not isinstance(eth.data, dpkt.ip.IP) and not isinstance(eth.data, dpkt.ip6.IP6):
                dpkt.arp.ARP
                # print('Non IP Packet type not supported %s\n' % eth.data.__class__.__name__)
                continue
                
            is_ipv4 = isinstance(eth.data, dpkt.ip.IP)

            ip = eth.data
            src_ip = inet_to_str(ip.src)
            dst_ip = inet_to_str(ip.dst)

            # mengecek pengirim dan penerima paket
            is_tx = self.is_same_network(src_ip)
            is_rx = self.is_same_network(dst_ip)
            
            if isinstance(ip.data, dpkt.tcp.TCP):
                src_port = ip.data.sport
                dst_port = ip.data.dport

            elif isinstance(ip.data, dpkt.udp.UDP):
                udp = ip.data
                src_port = udp.sport
                dst_port = udp.dport

                if udp.dport == 67 or udp.sport == 67 or udp.dport == 68 or udp.sport == 68:
                    dhcp = dpkt.dhcp.DHCP(udp.data)
                    if isinstance(dhcp, dpkt.dhcp.DHCP):
                        mac = mac_to_str(dhcp.chaddr)
                        option_host_name = 12
                        for opt in dhcp.opts:
                            if opt[0] == option_host_name:
                                value = binascii.hexlify(opt[1]).decode()
                                value = bytes.fromhex(value).decode()

                                curr = self.get_item(mac)
                                curr['host_name'] = value
                
                elif udp.dport == 53 or udp.sport == 53:
                    dns = dpkt.dns.DNS(udp.data)
                    if len(dns.an) > 0:
                        for d in dns.an:
                            if d.type == dpkt.dns.DNS_A:
                                dns_ip = inet_to_str(d.rdata)
                                domain = self.get_domain(dns_ip)
                                name = '.'.join(d.name.replace('www.', '').split('.')[-3:])

                                if name not in domain['name']:
                                    domain['name'].append(name)
            else:
                src_port = None
                dst_port = None

            if self.is_router:
                if is_ipv4:
                    if is_tx:
                        if src_mac == self.iface['mac']:
                            continue
                    elif is_rx:
                        if dst_mac == self.iface['mac'] and dst_ip == self.iface['ip']:
                            continue
                else:
                    if is_tx:
                        if src_mac == self.iface['mac']:
                            continue
                    elif is_rx:
                        if dst_mac == self.iface['mac'] and dst_ip == self.iface['ip6']:
                            continue
            else:
                if is_ipv4:
                    if is_tx:
                        if src_ip != self.iface['ip']:
                            continue
                    elif is_rx:
                        if dst_ip != self.iface['ip']:
                            continue
                else:
                    if is_tx:
                        if src_ip != self.iface['ip6']:
                            continue
                    elif is_rx:
                        if dst_ip != self.iface['ip6']:
                            continue

            
            if self.autoSaveCheckBox.isChecked():
                data_record = [
                    timestamp,
                    self.get_mac_ip_key(src_mac, src_ip)['id'],
                    self.get_mac_ip_key(dst_mac, dst_ip)['id'],
                    type(ip.data).__name__,
                    src_port,
                    dst_port,
                    packet_length
                ]
                self.data_temp.append(data_record) 
            
            if is_tx:
                curr = self.get_item(src_mac)

                if is_ipv4:
                    curr['ip'] = src_ip
                else:
                    curr['ip6'] = src_ip

                curr['tx_gap'] += packet_length
                curr['tx_length'] += packet_length

                domain = self.get_domain(dst_ip)
                domain['visited'] += 1
                domain['data_usage'] += packet_length

            elif is_rx:
                curr = self.get_item(dst_mac)
                
                if is_ipv4:
                    curr['ip'] = dst_ip
                else:
                    curr['ip6'] = dst_ip

                curr['rx_gap'] += packet_length
                curr['rx_length'] += packet_length

                domain = self.get_domain(src_ip)
                domain['visited'] += 1
                domain['data_usage'] += packet_length   
                

    def closeEvent(self, event):
        self.table_timer.stop()
        self.log_timer.stop()


if __name__ == "__main__":
    app = QApplication(sys.argv)
    dialog = App()
    dialog.show()
    sys.exit(app.exec_())

