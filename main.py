"""
Ohaus Scale Reader GUI
Reads weight data from an Ohaus scale over serial (RS-232).
Supports Ohaus Scout, Ranger, Pioneer, Adventurer, and other
scales that use the standard Ohaus serial protocol.

Requirements:
    pip install pyserial

Usage:
    python ohaus_scale_reader.py
"""
import pdb
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import serial
import serial.tools.list_ports
import threading
import time
import csv
import re
from datetime import datetime
import statistics
from collections import deque
import numpy as np
from scipy.signal import medfilt
from scipy.signal import order_filter

# ── Ohaus serial protocol constants ──────────────────────────────────────────
# Most Ohaus scales respond to "P\r\n" (print command) and stream data in the
# format:  [sign][digits].[digits] [unit]\r\n  e.g.  "   1.234 g\r\n"
# Some models stream continuously; others require a print command per reading.

PRINT_COMMAND = b"CP\r\n"       # Standard Ohaus print/send command
READ_TIMEOUT  = 2            # Seconds to wait for a response
POLL_INTERVAL = 0.5            # Seconds between auto-poll requests
MOPSS_CHECK_PERIOD=5*60*1000
COMMAND_TIMEOUT=3000

# ── Colour palette (works on all platforms) ───────────────────────────────────
CLR_BG        = "#f5f5f3"
CLR_SURFACE   = "#ffffff"
CLR_BORDER    = "#d8d7d0"
CLR_PRIMARY   = "#185FA5"
CLR_SUCCESS   = "#0F6E56"
CLR_DANGER    = "#A32D2D"
CLR_TEXT      = "#2c2c2a"
CLR_MUTED     = "#5f5e5a"

SCALE_PORT ="/dev/serial/by-id/usb-FTDI_FT230X_Basic_UART_DU0E1LSQ-if00-port0"
MOPPS_PORT ="/dev/serial/by-id/usb-Teensyduino_USB_Serial_13543560-if00"


class OhausScaleApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Ohaus/MOPPS Scale Reader")

        self.resizable(True, True)
        self.configure(bg=CLR_BG)
        self.protocol("WM_DELETE_WINDOW", self._close)
        self.minsize(480, 560)
        self.sampleSize=50
        self.stableSampleSize=20
        self.valuesList=deque([],maxlen=self.sampleSize)
        self.stableList=deque([],maxlen=self.stableSampleSize)
        self.measureRunning=False
        self.last_weight=None
        self.last_id=None
        self.last_temp=None
        self.last_stableWeight=None
        self.tareFlagg=False
        self.unsavedData=False
        self.commandResponse=0 #0=OKAY,1=waiting 2=error
        self.commandQueue=deque([],maxlen=10)
        # State
        self._scaleSerial: serial.Serial | None = None
        self._mopssSerial: serial.Serial | None = None
        self.timeLastWeight=0
        self.timeLastFreq=0
        self.timeLastCommandSent=0
        self.fetchingFreq=False

        self._running = False
        self._poll_thread: threading.Thread | None = None
        self._poll_thread_mopps: threading.Thread | None = None
        self._log: list[dict] = []          # [{timestamp, weight, unit}, ...]

        self._build_ui()
        
        self.after(300,self._connect)
        self.after(600,self._continuous_scale_loop)
        self.after(610,self._continuous_mopss_loop)

        

    # ── UI construction ───────────────────────────────────────────────────────

    def _build_ui(self):
        pad = dict(padx=16, pady=8)

      


        # ── Weight display ──
        weight_frame = tk.Frame(self, bg=CLR_SURFACE,
                                highlightbackground=CLR_BORDER,
                                highlightthickness=1)
        weight_frame.pack()
        weight_frame.rowconfigure(0, weight=1)
        weight_frame.rowconfigure(1, weight=1)
        weight_frame.rowconfigure(2, weight=1)
        weight_frame.columnconfigure(0, weight=1)
        weight_frame.columnconfigure(1, weight=3)
        weight_frame.columnconfigure(2, weight=1)
        
        self._status_var = tk.StringVar(value="—")
        self._weight_var = tk.StringVar(value="—")
        self._meas_var=tk.StringVar(value="N/A")
        self._id_var = tk.StringVar(value="Waiting for Scale")
        
        tk.Label(weight_frame, textvariable=self._id_var,
                 font=("Courier", 24, "bold"),
                 bg=CLR_SURFACE, fg=CLR_TEXT,
                 anchor="center").grid(column=0, row=0,columnspan=3)
        tk.Label(weight_frame, textvariable=self._meas_var,
                 font=("Courier", 52, "bold"),
                 bg=CLR_SURFACE, fg=CLR_TEXT,
                 anchor="center").grid(column=0, row=1,columnspan=3)

        
        tk.Label(weight_frame, textvariable=self._weight_var,
                 font=("Courier", 14, "bold"),
                 bg=CLR_SURFACE, fg=CLR_TEXT,width=15,
                 anchor="w").grid(column=0, row=2)
        self._unit_var = tk.StringVar(value="")

        self._stability_var = tk.StringVar(value="")
        tk.Label(weight_frame, textvariable=self._stability_var,
                 font=("", 9), bg=CLR_SURFACE,
                 fg=CLR_MUTED, anchor="e").grid(column=2, row=2)
        self.tareLabel=tk.Label(weight_frame, text="TARE",
                 font=("", 9), bg=CLR_SURFACE,
                 fg=CLR_MUTED, anchor="e")
        self.tareLabel.grid(column=1, row=2)

        self.pb = ttk.Progressbar(
                weight_frame,
                orient='horizontal',
                mode='determinate')
        self.pb.grid(column=0, row=3,columnspan=3,sticky='EW')
        

        # Manual read button
        manual_row = tk.Frame(self, bg=CLR_BG)
        manual_row.pack(fill="x", padx=16, pady=(0, 8))
        self._start_btn = tk.Button(manual_row, text="Start Reading",
                                  command=self._start_reading,
                                  bg=CLR_BG, fg=CLR_TEXT,
                                  relief="flat", padx=14, pady=6,
                                  font=("", 10), cursor="hand2",
                                  state="active",
                                  highlightbackground=CLR_BORDER,
                                  highlightthickness=1)
        self._start_btn.pack(side="left", padx=(8, 0))
        
        self._zero_btn = tk.Button(manual_row, text="Zero Scale",
                                  command=self._zero_scale,
                                  bg=CLR_BG, fg=CLR_TEXT,
                                  relief="flat", padx=14, pady=6,
                                  font=("", 10), cursor="hand2",
                                  state="normal",
                                  highlightbackground=CLR_BORDER,
                                  highlightthickness=1)
        self._zero_btn.pack(side="left", padx=(8, 0))
                
        self._tare_btn = tk.Button(manual_row, text="Tare Scale",
                                  command=self._tare_scale,
                                  bg=CLR_BG, fg=CLR_TEXT,
                                  relief="flat", padx=14, pady=6,
                                  font=("", 10), cursor="hand2",
                                  state="normal",
                                  highlightbackground=CLR_BORDER,
                                  highlightthickness=1)
        self._tare_btn.pack(side="left", padx=(8, 0))


        self._clearTag_btn = tk.Button(manual_row, text="Clear Data",
                                  command=self.clearTag,
                                  bg=CLR_BG, fg=CLR_TEXT,
                                  relief="flat", padx=14, pady=6,
                                  font=("", 10), cursor="hand2",
                                  state="normal",
                                  highlightbackground=CLR_BORDER,
                                  highlightthickness=1)
        self._clearTag_btn.pack(side="left", padx=(8, 0))

        tk.Button(manual_row, text="Export CSV",
                  command=self._export_csv,
                  bg=CLR_BG, fg=CLR_MUTED,
                  relief="flat", padx=14, pady=6,
                  font=("", 10), cursor="hand2").pack(side="right")

        # ── Log table ──
        log_frame = tk.LabelFrame(self, text=" Log ", bg=CLR_BG,
                                  fg=CLR_MUTED, font=("", 10),
                                  bd=1, relief="groove")
        log_frame.pack(fill="both", expand=True, padx=16, pady=(0, 0))

        cols = ("weight","stableWeight", "tagID","tagTemp","timestamp")
        self._tree = ttk.Treeview(log_frame, columns=cols,
                                  show="headings", height=8)
        
        
        self._tree.heading("weight",    text="Weigh [g]")
        self._tree.heading("stableWeight", text="Stable Weight[g][g]")
        self._tree.heading("tagID",      text="ID")
        self._tree.heading("tagTemp",      text="Temp [c]")
        self._tree.heading("timestamp", text="Timestamp")
        self._tree.column("weight",    width=100, anchor="e")
        self._tree.column("stableWeight", width=100, anchor="w")
        self._tree.column("tagID",      width=170,  anchor="w")
        self._tree.column("tagTemp",      width=40,  anchor="w")
        self._tree.column("timestamp", width=170, anchor="w")

        vsb = ttk.Scrollbar(log_frame, orient="vertical",
                            command=self._tree.yview)
        self._tree.configure(yscrollcommand=vsb.set)
        self._tree.pack(side="left", fill="both", expand=True, padx=(8, 0), pady=0)
        vsb.pack(side="right", fill="y", pady=0, padx=(0, 8))

        # Clear log button
        tk.Button(log_frame, text="Clear log", command=self._clear_log,
                  bg=CLR_BG, fg=CLR_MUTED, relief="flat",
                  font=("", 9), cursor="hand2").pack(anchor="se", padx=8, pady=(0, 6))
        self._freq_var = tk.StringVar(value="")
        self.freqLabel=tk.Label(self, textvariable=self._freq_var,
                 font=("", 9), bg=CLR_BG,
                 fg=CLR_MUTED, anchor="e",height=2)
        self.freqLabel.pack(fill="none", expand=False, padx=0, pady=(0, 0),ipady=0)


        # plt.ion()  # interactive mode
        # self.fig, self.ax = plt.subplots()
        # self.raw_line, = self.ax.plot([], [], label='Raw')
        # self.filtered_line, = self.ax.plot([], [], label='Filtered', linewidth=2)
        # self.ax.set_xlim(0, self.sampleSize)   # initial x-axis limit
        # self.ax.set_ylim(190, 210)  # adjust based on expected weights
        # self.ax.autoscale(True)
        # self.ax.set_xlabel("Sample")
        # self.ax.set_ylabel("Weight (kg)")
        # self.ax.legend()
        # plt.title("Real-Time Dynamic Animal Weight Filtering")


    def _start_reading(self):
        self.valuesList.clear()
        self.measureRunning=True
        self._tare_btn.config(state=tk.DISABLED)
        self._zero_btn.config(state=tk.DISABLED)
        self._clearTag_btn.config(state=tk.DISABLED)
        self._start_btn.config(state=tk.ACTIVE)

        return

    # ── Connection ────────────────────────────────────────────────────────────

    def _connect(self):
       
        try:
            self._scaleSerial = serial.Serial(
                port=SCALE_PORT,
                baudrate=115200,
                bytesize=8,
                parity=serial.PARITY_NONE,
                stopbits=1,
                timeout=READ_TIMEOUT,
            )
        except serial.SerialException as e:
            messagebox.showerror("Scale Connection failed", "Scale Could not be found.\nExiting")
            self._close()
            return
        try:
            self._mopssSerial = serial.Serial(
                port=MOPPS_PORT,
                baudrate=115200,
                bytesize=8,
                parity=serial.PARITY_NONE,
                stopbits=1,
                timeout=READ_TIMEOUT,
            )
        except serial.SerialException as e:
            messagebox.showerror("MoPSS Connection failed", "MoPSS Could not be found.\nExiting")
            self._close()
            return
        
        self._running = True




        # Colour the status label green — tkinter doesn't allow fg on StringVar labels
        # directly so we find it by walking the btn_row children
        for w in self.winfo_children():
            if isinstance(w, tk.LabelFrame):
                for child in w.winfo_children():
                    if isinstance(child, tk.Frame):
                        for grandchild in child.winfo_children():
                            if isinstance(grandchild, tk.Label) and \
                               "connected" in (grandchild.cget("textvariable") or "").lower():
                                pass  # updated via variable; colour set below
        
        # Start background thread
        #self._poll_thread = threading.Thread(target=self._continuous_scale_loop, daemon=True)
        #self._poll_thread.start()
        #self._poll_thread_mopps = threading.Thread(target=self._continuous_mopss_loop, daemon=True)
        #self._poll_thread_mopps.start()

        
        

        self.scaleCommand(b"ON")
        self.sendScaleCommand()
        count=0
        while 1:
            line = self._scaleSerial.readline().decode("ascii", errors="ignore").strip()
            #print(line)
            if line=="OK!":
                break
        self.commandQueue.popleft()
        self.scaleCommand(b"P")

        self.sendScaleCommand()
        while 1:
            line = self._scaleSerial.readline().decode("ascii", errors="ignore").strip()
            #print(line)
            if line=="ES":
                time.sleep(0.25)
                self.sendScaleCommand()
            elif line[:3]=="RRC":
                self.commandQueue.clear()
                self.commandResponse =0
                break
        _SCALE_RE = re.compile("^RRC .* Balance ID: (?P<balanceID>[\S]{10}) Balance Type: (?P<balanceType>[\S]*)")
        m = _SCALE_RE.search(line)

        self._mopssSerial.write(b'4')
        self.scaleCommand(b"1M")
        self.scaleCommand(b"1U")
        self.scaleCommand(b"CP",False)
        self._id_var.set("Waiting For Mouse")
        self.scaleID=m.group("balanceID").upper()
        self.scaleType=m.group("balanceType").upper()
        #self.title(self.scaleID)
        

        

    def scaleCommand(self,command,waitForResponse=True):       
        
        self.commandQueue.append((command,waitForResponse))
        
    def sendScaleCommand(self):
        try:
            self._scaleSerial.write(self.commandQueue[0][0] + b"\r\n")
           #print(b"Sending " + self.commandQueue[0][0])
            self.commandResponse=self.commandQueue[0][1]
            if self.commandResponse ==0:
                self.commandQueue.popleft()
            self.timeLastCommandSent=time.time()*1000
        except (OSError,serial.SerialException):
            self.after(0, self._on_scaleSerial_error)
    def _close(self):
        
        if (self.unsavedData):
            if not messagebox.askyesno("Quit", "There is unsaved data.\nDo you really want to quit?"):
                return
        self._running=False
        try:
            self._scaleSerial.cancel_read()
            self._mopssSerial.cancel_read()
        except:
            pass
        self._scaleSerial.write(b"0P\r\n")
        self._scaleSerial.write(b"OFF\r\n")

        if self._poll_thread and self._poll_thread.is_alive():
            self._poll_thread.join()
        if self._poll_thread_mopps  and  self._poll_thread_mopps.is_alive():
            self._poll_thread_mopps.join()
        if self._scaleSerial and self._scaleSerial.is_open:
            self._scaleSerial.close()
            self._scaleSerial = None
        if self._mopssSerial and self._mopssSerial.is_open:
            self._mopssSerial.close()
            self._mopssSerial = None
        self.destroy()
        
        

    def _continuous_scale_loop(self):
            
       # while self._running and self._scaleSerial and self._scaleSerial.is_open:
            try:
                
                if self.commandResponse==1 and ((int(time.time() * 1000)-self.timeLastCommandSent)>3000):

                    messagebox.showinfo("Command Timeout","Timeout Error")
                    self.commandQueue.popleft()
                    self.commandResponse=0
                if (self._scaleSerial.in_waiting == 0):
                    if len(self.commandQueue)>0 and self.commandResponse==0:
                        self.sendScaleCommand()
                    self.after(1,self._continuous_scale_loop)
                    return
                if ((int(time.time() * 1000)-self.timeLastWeight)>500):
                            self.scaleCommand(b"CP\r\n",False)
                
                
                           
            
                
                line = self._scaleSerial.readline().decode("ascii", errors="ignore").strip()

                
                
                if line and self._running:
                    self.timeLastWeight=int(time.time() * 1000)    
                    if len(self.commandQueue)>0:
                        if self.commandResponse==1:
                            if (line[:3]=="OK!"):
                                if self.commandQueue[0][0] in (b"T",b"Z"):
                                    self._id_var.set("Waiting For Mouse")
                                self.commandQueue.popleft()
                                self.commandResponse=0

                                raise StopIteration
                            elif(line[:2]=="ES"):
                                if self.commandQueue[0][0] in (b"T",b"Z"):
                                    messagebox.showinfo("Tare Failed","Check that something is on the scale")
                                    self.commandQueue.popleft()
                                    self.commandResponse=0
                                    
                                else:
                                    self.sendScaleCommand()
                                time.sleep(0.1)
                                raise StopIteration

                        
                    if(line[:2]=="ES" or line[:3]=="OK!"):
                        
                        raise StopIteration
                    self.after(0, self._parse_and_display, line)

                
            except (OSError,serial.SerialException) as ex:
                template = "An exception of type {0} occurred. Arguments:\n{1!r}"
                message = template.format(type(ex).__name__, ex.args)
                
                
                self.after(0, self._on_scaleSerial_error,message,"Scale Communication Error")
                return
                #break
            except:                
                pass
            
            self.after(1,self._continuous_scale_loop)


    def _continuous_mopss_loop(self):
            try:
                if ((int(time.time() * 1000)-self.timeLastFreq)>MOPSS_CHECK_PERIOD) and self.fetchingFreq==False:
                        self._getMopssFreq()
                        self.fetchingFreq=True
                if (self._mopssSerial.in_waiting == 0):
                    
                    self.after(1,self._continuous_mopss_loop)
                    return
                
                """Read lines as they arrive (for scales set to continuous output mode)."""
            #while self._running and self._mopssSerial and self._mopssSerial.is_open:       
                
            
                
                line = self._mopssSerial.readline().decode("ascii", errors="ignore").strip()
                print (line)
                
                
                
                if line and self._running:
                    self.after(0, self._parse_mopps, line)
                    if (line[:4] == "FREQ"):
                        self.timeLastFreq=int(time.time() * 1000)
                        self.fetchingFreq=False
            
            except (OSError,serial.SerialException) as ex:
                template = "An exception of type {0} occurred. Arguments:\n{1!r}"
                message = template.format(type(ex).__name__, ex.args)
                
                self.after(0, self._on_scaleSerial_error,message,"MoPSS Communication Error")
                return
                
                #break
        
            self.after(1,self._continuous_mopss_loop)

    def clearTag(self):
        self._id_var.set("Please Insert Mouse")
        self._meas_var.set("N/A")

    _MOPPS_RE = re.compile(r"RA1,\d*,(?P<id>\d{3}_\d*),(?P<temp>\d*),\d*,(?P<movement>[EX])")
    
    def _parse_mopps(self, raw: str):
        raw = raw.strip()
        if (self._running):
            if (raw[:3]=="RA1"):
                try:
                    m = self._MOPPS_RE.search(raw)
                except re.error as e:
                    print(f"Regex Error: {e}")
                move=m.group("movement").upper()
                if (move == "E"):
                    tagID=m.group("id").upper()
                    tagTemp=m.group("temp").upper()
                    self._id_var.set(tagID)
                    self.last_id=tagID
                    self.last_temp=((int(tagTemp)*0.2+74)-32)*5/9
            elif (raw[:4]=="FREQ"):
                freq=float(raw[6:])/1000.0
                self._freq_var.set(f"MoPSS Freq.: {freq:+3.1f} kHz")
                if (abs(freq-134.2)<1):
                    self.freqLabel.config(fg="green")
                else:
                    self.freqLabel.config(fg="red")
                    self._freq_var.set(f"MoPSS Freq.: {freq:+3.1f} kHz\nAntenna Detuned!")
        return


    _WEIGHT_RE = re.compile(
#        r"Final wt.:\s*(?P<sign>[+-]?)\s*(?P<value>[\d]+\.?[\d]*)\s+(?P<unit>\w+)\s*(?P<stable>[?]{0,2})\s*(?P<net>N?)"    )
        r"(?P<sign>[+-]?)\s*(?P<value>[\d]+\.?[\d]*)\s+(?P<unit>\w+)\s*(?P<stable>[?]{0,2})\s*(?P<net>N?)"    )

    def _parse_and_display(self, raw: str):
        
        raw = raw.strip()
        
        if raw.upper() in ("OVER LOAD", "UNDER LOAD", "ERR") and self._running:
            self._weight_var.set(raw.upper())

            self._stability_var.set("⚠ Scale error / out of range")
            return

        
        
        try:
            m = self._WEIGHT_RE.search(raw)
            
        except re.error as e:
            print(f"Regex Error: {e}")
        

        
        if not m:
            if (self._running):
                self._stability_var.set(f"Unrecognised: {raw}")
            return  

        stable_flag = m.group("stable").upper()
        value       = float((m.group("sign") + m.group("value")).replace(" ", ""))
        netFlag      = m.group("net")
        if (self._running):
            self._weight_var.set(f"{value:+2f} g" if value < 0 else f"{value:.2f} g")
            
            if "?" in stable_flag:
                self._stability_var.set("⟳ Unstable")
            elif "" in stable_flag or stable_flag == "":
                self._stability_var.set("✓ Stable")    
            if "N" in netFlag:
                self.tareLabel.grid(column=1, row=2)
            elif "" in netFlag or netFlagg == "":
                self.tareLabel.grid_forget()    
        if self.measureRunning:
            self.valuesList.append(value)
            filtered = []
            window_size = 9  # number of samples in the filter
            rank = 4         # 0 = min, (window_size-1)//2 = median, window_size-1 = max
            self.pb['value']=100*len(self.valuesList)/self.sampleSize
            if len(self.valuesList) >window_size :
                    filtered_value = order_filter(self.valuesList, np.ones(window_size), rank)
            med=statistics.median(self.valuesList)
            if (self._running):
                self._meas_var.set(f"{med:+2f} g" if med < 0 else f"{med:.2f} g")

            if "" in stable_flag or stable_flag == "":
                self.stableList.append(value)
                #print(self.stableList)
            # self.raw_line.set_data(range(len(self.valuesList)),self.valuesList)
            # self.filtered_line.set_data(range(len(filtered_value)), filtered_value)
            # self.ax.relim()
            # self.ax.autoscale_view()
            if (len(self.valuesList)==self.sampleSize):
                self.measureRunning=False
                self.last_weight=statistics.median(self.valuesList)
                self.last_stableWeight=statistics.median(self.stableList)
                if (self._running):
                    self._meas_var.set(f"{self.last_weight:+2f} g" if self.last_weight < 0 else f"{self.last_weight:.2f} g")
                    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
                    row = {"weight": self.last_weight,"stableWeight":self.last_stableWeight, "ID": self.last_id, "Temp":self.last_temp,"timestamp": ts,}
                    self._log.append(row)
                    self._tree.insert("", "end", values=(f"{self.last_weight:.2f}",f"{self.last_stableWeight:.2f}", self.last_id,self.last_temp,ts))
                    self._tree.yview_moveto(1)
                    self._tare_btn.config(state=tk.NORMAL)
                    self._zero_btn.config(state=tk.NORMAL)
                    self._clearTag_btn.config(state=tk.NORMAL)
                    self._start_btn.config(state=tk.NORMAL)
                    self.unsavedData=True
                    self.title("Ohaus/MOPPS Scale Reader *")

        # print(statistics.mode(self.valuesList))
        # print(statistics.median(self.valuesList))
        # print(statistics.variance(self.valuesList))        
        # # Step 1: Median filter to remove spikes
        # median_filtered = medfilt(self.valuesList, kernel_size=5)

        # # Step 2: Identify stable values close to baseline
        # # We assume the true weight is near the minimum median value
        # baseline = statistics.median(median_filtered)
        # print("base:",baseline)
        # # Step 3: Select measurements within a small range of the baseline
        # stable_values = [x for x in median_filtered if abs(x - baseline) < 2.0]

        # # Step 4: Compute the final estimate as the mean of stable values
        # true_weight_estimate = np.median(stable_values)

        # print("Estimated true weight:", true_weight_estimate)
        

        # Store last parsed reading for log button
        
    def _on_scaleSerial_error(self,message=None,title=None):
        self._status_var.set("● Connection lost")
        self._weight_var.set("ERR")
        
        if self.unsavedData:
            messagebox.askyesno(title,message+"\n Do you want to save your data?")
            self._export_csv()
        else:
            messagebox.showerror(title,message)
        self._close()
        


    # ── Logging ───────────────────────────────────────────────────────────────
    def _zero_scale(self):
        self._id_var.set("Zeroing...")
        self.scaleCommand(b"0P")
        self.scaleCommand(b"Z")
        self.scaleCommand(b"CP",False)
    def _tare_scale(self):
        self._id_var.set("Taring...")
        self.scaleCommand(b"0P")
        self.scaleCommand(b"T")
        self.scaleCommand(b"CP",False)
    def _singleRead(self):
        self.scaleCommand(b"IP",False)
    def _getMopssFreq(self):
        
        try:
            
            self._mopssSerial.write(b"4\r\n")
            self.freqLabel.config(fg=CLR_PRIMARY)
            self._freq_var.set("Fetching MoPSS Frequency")
        except serial.SerialException:
            self.after(0, self._on_scaleSerial_error)
    def _clear_log(self):
        self._log.clear()
        for item in self._tree.get_children():
            self._tree.delete(item)
        self.unsavedData=False
        self.title("Ohaus/MOPPS Scale Reader")

    def _export_csv(self):
        print(self._log)
        if not self._log:
            messagebox.showinfo("Nothing to export", "Log is empty.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
            title="Save log as CSV",
        )
        if not path:
            return
        with open(path, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=["timestamp", "weight", "stableWeight","ID", "Temp"])
            writer.writeheader()
            writer.writerows(self._log)
        messagebox.showinfo("Exported", f"Saved {len(self._log)} rows to:\n{path}")
        self.unsavedData=False
        self.title("Ohaus/MOPPS Scale Reader")

    # ── Cleanup ───────────────────────────────────────────────────────────────

    def destroy(self):
        self._running = False
        if self._scaleSerial and self._scaleSerial.is_open:
            self._scaleSerial.close()
        super().destroy()


if __name__ == "__main__":
    app = OhausScaleApp()
    
    app.mainloop()