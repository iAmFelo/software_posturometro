# posturometro_app_v3_autocom.py
# Requisitos:
#   pip install PySide6 pyqtgraph pyserial
#
# Arduino debe enviar 14 valores por línea:
# p0,p1,p2,p3,p4,p5,xg,yg,xl,yl,xr,yr,PL,PR

import os, sys, time, csv, json, sqlite3, re, math
from dataclasses import dataclass
from datetime import datetime, date
from collections import deque

import serial
import serial.tools.list_ports

from PySide6 import QtWidgets, QtCore
import pyqtgraph as pg


# ===================== CONFIG (EDITABLE) =====================
BAUD = 115200

DATA_DIR = "data"
DB_PATH = os.path.join(DATA_DIR, "pacientes.db")
PATIENTS_DIR = os.path.join(DATA_DIR, "Pacientes")

FRAME_LEN = 14
EMA_ALPHA = 0.12

# Zoom del gráfico principal (para ver cambios finos)
PLOT_RANGE = 15  # -> X,Y = [-15..+15]
X_MIN, X_MAX = -PLOT_RANGE, PLOT_RANGE
Y_MIN, Y_MAX = -PLOT_RANGE, PLOT_RANGE

# Zoom de trazados en comparativo (más cercano)
CMP_TRAIL_X_RANGE = 45
CMP_TRAIL_Y_RANGE = 12
CMP_PANEL_OFFSETS = {"L": -30.0, "G": 0.0, "R": 30.0}

# Longitud de trayectoria (más corto = más “limpio”)
TRAIL_LEN = 800

# Métricas sobre ventana móvil
METRIC_WINDOW = 500

# Tamaños de puntos
COP_DOT_SIZE_G = 16
COP_DOT_SIZE_F = 14
KAP_DOT_SIZE = 22


# Umbral de carga total para considerar "sin apoyo" en Kapandji
KAP_NO_SUPPORT_PT = 1.0

# Pesos Kapandji esperados por zona (TOP, SIDE, HEEL)
KAP_WEIGHTS = (2.0 / 6.0, 1.0 / 6.0, 3.0 / 6.0)

# Baselines esperados en porcentaje (solo referencia clínica)
KAP_BASELINE_BY_POINT = {
    "L_med": 100.0 * KAP_WEIGHTS[0],
    "R_med": 100.0 * KAP_WEIGHTS[0],
    "L_lat": 100.0 * KAP_WEIGHTS[1],
    "R_lat": 100.0 * KAP_WEIGHTS[1],
    "L_heel": 100.0 * KAP_WEIGHTS[2],
    "R_heel": 100.0 * KAP_WEIGHTS[2],
}

# Tolerancia clínica relativa para score vs esperado
KAP_TOLERANCE = 0.20

# Umbrales de score por desvío relativo contra esperado
# Regla general (TOP/HEEL): verde < 0.80, amarillo 0.80-1.20, rojo > 1.20
KAP_SCORE_GREEN_MAX = 1.0 - KAP_TOLERANCE
KAP_SCORE_RED_MIN = 1.0 + KAP_TOLERANCE

# SIDE suele ser más variable: umbrales más tolerantes
KAP_SCORE_BOUNDS_BY_POINT = {
    "L_lat": (0.75, 1.25),
    "R_lat": (0.75, 1.25),
}

# Mostrar ratio (real/esperado) además del valor real en cada punto Kapandji
SHOW_KAP_RATIO = False
# Factor opcional de conversión a kg (None = no convertir, usar unidades crudas)
KAP_SCALE_FACTOR = None
# Unidad a mostrar para valor crudo ("u", "counts" o "")
KAP_VALUE_UNIT = "u"

KAP_COLOR_GREEN = (60, 200, 90)
KAP_COLOR_YELLOW = (240, 200, 0)
KAP_COLOR_RED = (220, 50, 50)
KAP_COLOR_NEUTRAL = (140, 140, 140)

# PAUSA también frena grabación
PAUSE_STOPS_RECORDING_WRITE = True

# Autoconexión al abrir la app
AUTO_CONNECT_ON_START = True

# Cambiar sentido de torsion (T/F)
INVERT_TORSION_SIGN = False  # ponelo True si la torsión sale al revés

# Condiciones disponibles y colores
CONDITION_DEFS = [
    {"code": "NO", "label": "Postura (NO)", "short": "NO", "color": "c", "color_html": "cyan"},
    {"code": "OCC", "label": "Boca (OCC)", "short": "OCC", "color": "y", "color_html": "yellow"},
    {"code": "CE", "label": "Pie (CE)", "short": "CE", "color": "m", "color_html": "magenta"},
    {"code": "BED", "label": "Bed (BED)", "short": "BED", "color": (255, 140, 0), "color_html": "#ff8c00"},
    {"code": "BEDC", "label": "Bed Corregido (BEDC)", "short": "BEDC", "color": (128, 96, 255), "color_html": "#8060ff"},
]
CONDITION_CODES = [c["code"] for c in CONDITION_DEFS]
CONDITION_BY_CODE = {c["code"]: c for c in CONDITION_DEFS}


# ===================== UTIL =====================
def ensure_dirs():
    os.makedirs(DATA_DIR, exist_ok=True)
    os.makedirs(PATIENTS_DIR, exist_ok=True)

def slugify(name: str) -> str:
    name = name.strip()
    name = re.sub(r'[<>:"/\\|?*\n\r\t]', " ", name)
    name = re.sub(r"\s+", " ", name)
    return name

def now_stamp():
    return datetime.now().strftime("%Y-%m-%d_%H-%M-%S")

def parse_date_dd_mm_yyyy_or_yy(s: str):
    """
    Acepta:
      DD-MM-AAAA
      DD-MM-AA
    Guarda internamente YYYY-MM-DD.
    """
    s = s.strip()
    if not s:
        return None
    m = re.match(r"^(\d{2})-(\d{2})-(\d{2}|\d{4})$", s)
    if not m:
        return None
    dd = int(m.group(1)); mm = int(m.group(2)); yy = m.group(3)
    if len(yy) == 2:
        y = int(yy)
        year = 2000 + y if y <= 29 else 1900 + y
    else:
        year = int(yy)
    try:
        return date(year, mm, dd)
    except:
        return None

def age_years(dob: date) -> int | None:
    if dob is None:
        return None
    today = date.today()
    years = today.year - dob.year
    if (today.month, today.day) < (dob.month, dob.day):
        years -= 1
    return years

def kap_expected_for_key(key: str, PL: float, PR: float):
    if key.startswith("L_"):
        foot_total = PL
    else:
        foot_total = PR

    if key.endswith("med"):
        w = KAP_WEIGHTS[0]
    elif key.endswith("lat"):
        w = KAP_WEIGHTS[1]
    else:
        w = KAP_WEIGHTS[2]
    return foot_total * w

def kap_color_by_point(key: str, value: float, PL: float, PR: float):
    expected = kap_expected_for_key(key, PL, PR)
    if expected <= 1e-9:
        return KAP_COLOR_NEUTRAL
    ratio = value / expected
    green_max, red_min = KAP_SCORE_BOUNDS_BY_POINT.get(key, (KAP_SCORE_GREEN_MAX, KAP_SCORE_RED_MIN))
    if ratio < green_max:
        return KAP_COLOR_GREEN
    if ratio > red_min:
        return KAP_COLOR_RED
    return KAP_COLOR_YELLOW

def kap_point_label(key: str, value: float, PL: float, PR: float):
    shown = value * KAP_SCALE_FACTOR if KAP_SCALE_FACTOR is not None else value
    if KAP_SCALE_FACTOR is not None:
        unit = "kg"
    else:
        unit = KAP_VALUE_UNIT.strip()

    if unit:
        label = f"{shown:0.1f} {unit}"
    else:
        label = f"{shown:0.1f}"

    if not SHOW_KAP_RATIO:
        return label
    expected = kap_expected_for_key(key, PL, PR)
    if expected <= 1e-9:
        return label
    ratio = value / expected
    return f"{label}\n({ratio:0.2f}x)"



# ===================== DB =====================
def db_connect():
    ensure_dirs()
    con = sqlite3.connect(DB_PATH)
    con.execute("""
        CREATE TABLE IF NOT EXISTS patients (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            full_name TEXT NOT NULL UNIQUE,
            dob TEXT,
            created_at TEXT NOT NULL
        )
    """)
    try:
        cols = [r[1] for r in con.execute("PRAGMA table_info(patients)").fetchall()]
        if "dob" not in cols:
            con.execute("ALTER TABLE patients ADD COLUMN dob TEXT")
            con.commit()
    except:
        pass
    con.commit()
    return con

def db_add_patient(con, full_name: str, dob_iso: str | None):
    full_name = slugify(full_name)
    if not full_name:
        raise ValueError("Nombre vacío")
    con.execute("INSERT INTO patients(full_name, dob, created_at) VALUES (?,?,?)",
                (full_name, dob_iso, datetime.now().isoformat(timespec="seconds")))
    con.commit()

def db_delete_patient(con, patient_id: int):
    con.execute("DELETE FROM patients WHERE id=?", (patient_id,))
    con.commit()

def db_list_patients(con):
    cur = con.execute("SELECT id, full_name, dob, created_at FROM patients ORDER BY full_name COLLATE NOCASE")
    return cur.fetchall()


# ===================== SIGNAL PROCESSING =====================
class EMA:
    def __init__(self, alpha=0.1):
        self.alpha = alpha
        self.v = None
    def update(self, x):
        if self.v is None:
            self.v = x
        else:
            self.v = self.alpha * x + (1 - self.alpha) * self.v
        return self.v

@dataclass
class Metrics:
    sway_path: float = 0.0
    mean_speed: float = 0.0
    rms_x: float = 0.0
    rms_y: float = 0.0

class MetricWindow:
    def __init__(self, maxlen=500):
        self.buf = deque(maxlen=maxlen)  # (t, x, y)
    def add(self, t, x, y):
        self.buf.append((t, x, y))
    def compute(self) -> Metrics:
        if len(self.buf) < 3:
            return Metrics()
        dist = 0.0
        for i in range(1, len(self.buf)):
            _, x0, y0 = self.buf[i-1]
            _, x1, y1 = self.buf[i]
            dx, dy = x1 - x0, y1 - y0
            dist += (dx*dx + dy*dy) ** 0.5
        dt = max(1e-6, self.buf[-1][0] - self.buf[0][0])
        mean_speed = dist / dt
        xs = [p[1] for p in self.buf]
        ys = [p[2] for p in self.buf]
        mx = sum(xs)/len(xs)
        my = sum(ys)/len(ys)
        rms_x = (sum((x-mx)**2 for x in xs)/len(xs))**0.5
        rms_y = (sum((y-my)**2 for y in ys)/len(ys))**0.5
        return Metrics(dist, mean_speed, rms_x, rms_y)


# ===================== DIALOGS =====================
class AddPatientDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Nuevo paciente")
        self.setModal(True)
        layout = QtWidgets.QFormLayout(self)

        self.edit_name = QtWidgets.QLineEdit()
        self.edit_name.setPlaceholderText("Apellido Nombre (ej: Pérez Ana)")
        layout.addRow("Nombre:", self.edit_name)

        self.edit_dob = QtWidgets.QLineEdit()
        self.edit_dob.setPlaceholderText("DD-MM-AA o DD-MM-AAAA (ej: 25-07-80)")
        layout.addRow("Nacimiento:", self.edit_dob)

        btns = QtWidgets.QHBoxLayout()
        ok = QtWidgets.QPushButton("Guardar")
        cancel = QtWidgets.QPushButton("Cancelar")
        ok.clicked.connect(self.accept)
        cancel.clicked.connect(self.reject)
        btns.addWidget(ok); btns.addWidget(cancel)
        layout.addRow(btns)

    def values(self):
        name = self.edit_name.text().strip()
        dob_raw = self.edit_dob.text().strip()
        dob = parse_date_dd_mm_yyyy_or_yy(dob_raw) if dob_raw else None
        if dob_raw and dob is None:
            raise ValueError("Fecha inválida. Usá DD-MM-AA o DD-MM-AAAA")
        return name, (dob.isoformat() if dob else None)

class NewSessionDialog(QtWidgets.QDialog):
    def __init__(self, patient_name: str, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Nueva grabación")
        self.setModal(True)
        layout = QtWidgets.QFormLayout(self)

        layout.addRow("Paciente:", QtWidgets.QLabel(f"<b>{patient_name}</b>"))

        self.edit_name = QtWidgets.QLineEdit()
        self.edit_name.setPlaceholderText("Nombre sesión (ej: Control 1 - Marzo)")
        layout.addRow("Sesión:", self.edit_name)

        self.combo_cond = QtWidgets.QComboBox()
        self.combo_cond.addItems([c["label"] for c in CONDITION_DEFS])
        layout.addRow("Condición:", self.combo_cond)

        self.chk_clear = QtWidgets.QCheckBox("Limpiar trayectorias al iniciar")
        self.chk_clear.setChecked(True)
        layout.addRow("", self.chk_clear)

        btns = QtWidgets.QHBoxLayout()
        ok = QtWidgets.QPushButton("Iniciar")
        cancel = QtWidgets.QPushButton("Cancelar")
        ok.clicked.connect(self.accept)
        cancel.clicked.connect(self.reject)
        btns.addWidget(ok); btns.addWidget(cancel)
        layout.addRow(btns)

    def session_name(self):
        s = self.edit_name.text().strip()
        return s if s else "Sesion"
    def condition(self):
        return self.combo_cond.currentText()
    def clear_trails(self):
        return self.chk_clear.isChecked()



def normalize_condition(cond_text: str) -> str:
    """Convierte textos como 'Postura (NO)' a 'NO'."""
    if not cond_text:
        return "?"
    t = cond_text.strip().upper()
    if "BED CORREGIDO" in t or "BEDC" in t:
        return "BEDC"
    for key in CONDITION_CODES:
        if key in t:
            return key
    return cond_text.strip()

# ===================== PORT DETECTION =====================
def port_score(p) -> int:
    """
    Scoring heurístico para elegir el puerto "más probable" del Arduino.
    Más puntaje => más probable.
    """
    score = 0
    desc = (p.description or "").lower()
    mfg = (p.manufacturer or "").lower()
    hwid = (p.hwid or "").lower()

    # Arduino / USB Serial / CH340
    keywords = [
        "arduino", "usb serial", "serial", "wch", "ch340", "cp210", "silabs",
        "ftdi", "usb-serial", "usb to uart"
    ]
    for k in keywords:
        if k in desc or k in mfg or k in hwid:
            score += 20

    # VID/PID presente suma
    if p.vid is not None and p.pid is not None:
        score += 15

    # Si es un COM alto, a veces es el USB reciente (heurística liviana)
    try:
        if p.device.upper().startswith("COM"):
            n = int(p.device[3:])
            score += min(10, max(0, n - 3))
    except:
        pass

    return score

def pick_best_port(ports):
    if not ports:
        return None
    ranked = sorted(ports, key=port_score, reverse=True)
    best = ranked[0]
    # si el mejor tiene puntaje muy bajo, igual devolvemos pero con cautela
    return best.device


# ===================== MAIN APP =====================
class MainWindow(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        ensure_dirs()
        self.con = db_connect()

        self.setWindowTitle("Posturómetro - COP + Kapandji + Torsión")

        # Serial
        self.ser = None
        self.serial_ok = False
        self.current_port = None

        # Estado
        self.paused = False
        self.recording = False
        self.session_condition = "NO"
        self.current_patient = None  # (id, name, dob_iso)
        self.current_session_dir = None
        self.csv_file = None
        self.csv_writer = None

        # EMA
        self.ema_xg = EMA(EMA_ALPHA); self.ema_yg = EMA(EMA_ALPHA)
        self.ema_xl = EMA(EMA_ALPHA); self.ema_yl = EMA(EMA_ALPHA)
        self.ema_xr = EMA(EMA_ALPHA); self.ema_yr = EMA(EMA_ALPHA)

        # Trails
        self.trail_g = deque(maxlen=TRAIL_LEN)
        self.trail_l = deque(maxlen=TRAIL_LEN)
        self.trail_r = deque(maxlen=TRAIL_LEN)

        # Métricas
        self.metric_win = MetricWindow(maxlen=METRIC_WINDOW)

        # Último frame
        self.last_processed = None
        self.recent = deque(maxlen=METRIC_WINDOW)

        # Capturas estabilizadas por condición
        self.snapshots = {code: None for code in CONDITION_CODES}
        self.cmp_trails = {}  # {"NO":{"L":[(x,y)],"G":[...],"R":[...]}, ...}

        # ===== Replay animado =====
        self.replay_data = None  # dict con arrays
        self.replay_idx = 0
        self.replay_playing = False
        self.replay_speed = 1.0

        self.replay_timer = QtCore.QTimer()
        self.replay_timer.timeout.connect(self.replay_tick)
        self.replay_timer.setInterval(20)  # ~50 fps base

        self._build_ui()
        self._load_patients()

        # Autodetección y autoconexión
        self.refresh_com_ports()
        if AUTO_CONNECT_ON_START:
            self.auto_connect()

        self.timer = QtCore.QTimer()
        self.timer.timeout.connect(self.update_loop)
        self.timer.start(15)

        self._sidebar_prev_w = 320

    # ---------- UI ----------
    def _build_ui(self):
        cw = QtWidgets.QWidget()
        self.setCentralWidget(cw)
        root = QtWidgets.QHBoxLayout(cw)
        root.setContentsMargins(0, 0, 0, 0)

        # Splitter principal
        self.splitter = QtWidgets.QSplitter(QtCore.Qt.Horizontal)
        root.addWidget(self.splitter, 1)

        # ========== Sidebar (izquierda) ==========
        self.sidebar = QtWidgets.QWidget()
        left = QtWidgets.QVBoxLayout(self.sidebar)

        # ========== Main area (derecha) ==========
        self.main_area = QtWidgets.QWidget()
        right = QtWidgets.QVBoxLayout(self.main_area)

        # Agregar ambos al splitter
        self.splitter.addWidget(self.sidebar)
        self.splitter.addWidget(self.main_area)
        self.splitter.setStretchFactor(0, 0)
        self.splitter.setStretchFactor(1, 1)
        self.splitter.setSizes([320, 1000])

        left.addWidget(QtWidgets.QLabel("<b>Pacientes</b>"))
        self.list_patients = QtWidgets.QListWidget()
        self.list_patients.currentRowChanged.connect(self.on_patient_selected)
        left.addWidget(self.list_patients, 1)

        self.lbl_patient_info = QtWidgets.QLabel("Nacimiento: -- | Edad: --")
        left.addWidget(self.lbl_patient_info)

        rowp = QtWidgets.QHBoxLayout()
        self.btn_add = QtWidgets.QPushButton("Nuevo Paciente")
        self.btn_del = QtWidgets.QPushButton("Eliminar Paciente")
        self.btn_add.clicked.connect(self.add_patient)
        self.btn_del.clicked.connect(self.delete_patient)
        rowp.addWidget(self.btn_add); rowp.addWidget(self.btn_del)
        left.addLayout(rowp)

        left.addSpacing(10)
        left.addWidget(QtWidgets.QLabel("<b>Sesiones</b>"))
        self.list_sessions = QtWidgets.QListWidget()
        self.list_sessions.setSelectionMode(QtWidgets.QAbstractItemView.ExtendedSelection)

        left.addWidget(self.list_sessions, 1)

        self.btn_replay = QtWidgets.QPushButton("Replay (síntesis)")
        self.btn_replay.clicked.connect(self.replay_selected_session)
        left.addWidget(self.btn_replay)

        self.btn_cmp_from_sessions = QtWidgets.QPushButton("Comparar (Post/Boca/Pie)")
        self.btn_cmp_from_sessions.clicked.connect(self.compare_from_selected_sessions)
        left.addWidget(self.btn_cmp_from_sessions)

        topbar = QtWidgets.QHBoxLayout()
        right.addLayout(topbar)

        self.btn_toggle_sidebar = QtWidgets.QPushButton("⟨⟨")
        self.btn_toggle_sidebar.setFixedWidth(50)
        self.btn_toggle_sidebar.clicked.connect(self.toggle_sidebar)
        topbar.addWidget(self.btn_toggle_sidebar)

        # Selector COM + refresh
        self.combo_com = QtWidgets.QComboBox()
        topbar.addWidget(self.combo_com)

        self.btn_refresh_ports = QtWidgets.QPushButton("Actualizar COM")
        self.btn_refresh_ports.clicked.connect(self.refresh_com_ports)
        topbar.addWidget(self.btn_refresh_ports)

        self.btn_connect = QtWidgets.QPushButton("Conectar")
        self.btn_connect.clicked.connect(self.toggle_connection)
        topbar.addWidget(self.btn_connect)

        self.lbl_serial = QtWidgets.QLabel("Posturómetro desconectado")
        self.lbl_serial.setStyleSheet("color: red; font-weight: bold;")
        topbar.addWidget(self.lbl_serial, 1)

        self.lbl_rec = QtWidgets.QLabel("REC")
        self.lbl_rec.setStyleSheet("color: red; font-weight: bold;")
        self.lbl_rec.setVisible(False)
        topbar.addWidget(self.lbl_rec)

        self.btn_new_session = QtWidgets.QPushButton("Nueva grabación")
        self.btn_new_session.clicked.connect(self.start_new_session)
        topbar.addWidget(self.btn_new_session)

        self.btn_stop = QtWidgets.QPushButton("Parar grabacion")
        self.btn_stop.clicked.connect(self.stop_recording)
        self.btn_stop.setEnabled(False)
        topbar.addWidget(self.btn_stop)

        self.btn_pause = QtWidgets.QPushButton("PAUSA")
        self.btn_pause.setCheckable(True)
        self.btn_pause.clicked.connect(self.toggle_pause)
        topbar.addWidget(self.btn_pause)

        self.btn_clear = QtWidgets.QPushButton("Limpiar")
        self.btn_clear.clicked.connect(self.clear_all)
        topbar.addWidget(self.btn_clear)

        info = QtWidgets.QHBoxLayout()
        right.addLayout(info)

        self.balance = QtWidgets.QProgressBar()
        self.balance.setRange(0, 100)
        self.balance.setValue(50)
        self.balance.setFormat("Balance: %p% Der (Izq = 100-%p)")
        info.addWidget(self.balance, 1)

        self.lbl_weights = QtWidgets.QLabel("PL: --- | PR: --- | Izq: ---% Der: --- % | Overload: ---")
        info.addWidget(self.lbl_weights)

        self.lbl_metrics = QtWidgets.QLabel("Sway: - | Vel: - | RMSx: - | RMSy: - | Torsión: -°")
        self.lbl_metrics.setStyleSheet("font-family: Consolas, monospace;")
        right.addWidget(self.lbl_metrics)

        self.tabs = QtWidgets.QTabWidget()
        right.addWidget(self.tabs, 1)

        # ---- Tab: COP + Kapandji ----
        self.tab_live = QtWidgets.QWidget()
        v1 = QtWidgets.QVBoxLayout(self.tab_live)

        cap_row = QtWidgets.QHBoxLayout()
        v1.addLayout(cap_row)
        self.capture_buttons = {}
        for cond in CONDITION_DEFS:
            code = cond["code"]
            btn = QtWidgets.QPushButton(f"Capturar {cond['label']}")
            btn.clicked.connect(lambda _, c=code: self.capture_condition(c))
            cap_row.addWidget(btn)
            self.capture_buttons[code] = btn
        cap_row.addStretch(1)

        self.plot_live = pg.PlotWidget()
        self.plot_live.setLabel("bottom", "X (cm)")
        self.plot_live.setLabel("left", "Y (cm)")
        self.plot_live.setXRange(X_MIN, X_MAX)
        self.plot_live.setYRange(Y_MIN, Y_MAX)
        self.plot_live.showGrid(x=True, y=True, alpha=0.2)
        v1.addWidget(self.plot_live, 1)

        self.zero_y = pg.InfiniteLine(pos=0, angle=0, pen=pg.mkPen("w", width=1))
        self.zero_x = pg.InfiniteLine(pos=0, angle=90, pen=pg.mkPen("w", width=1))
        self.plot_live.addItem(self.zero_y)
        self.plot_live.addItem(self.zero_x)

        self.curve_g = self.plot_live.plot([], [], pen=pg.mkPen("r", width=2))
        self.curve_l = self.plot_live.plot([], [], pen=pg.mkPen("c", width=2))
        self.curve_r = self.plot_live.plot([], [], pen=pg.mkPen("g", width=2))

        self.dot_g = pg.ScatterPlotItem(size=COP_DOT_SIZE_G, brush=pg.mkBrush("r"), pen=pg.mkPen(None))
        self.dot_l = pg.ScatterPlotItem(size=COP_DOT_SIZE_F, brush=pg.mkBrush("c"), pen=pg.mkPen(None))
        self.dot_r = pg.ScatterPlotItem(size=COP_DOT_SIZE_F, brush=pg.mkBrush("g"), pen=pg.mkPen(None))
        self.plot_live.addItem(self.dot_g)
        self.plot_live.addItem(self.dot_l)
        self.plot_live.addItem(self.dot_r)

        self.kap_items = []
        self.kap_text_items = []
        self._init_kapandji_overlay()

        self.tabs.addTab(self.tab_live, "COP + Kapandji")

        # ---- Tab: Torsión ----
        self.tab_tor = QtWidgets.QWidget()
        v2 = QtWidgets.QVBoxLayout(self.tab_tor)

        self.plot_tor = pg.PlotWidget()
        self.plot_tor.setAspectLocked(True)
        self.plot_tor.setXRange(-25, 25)
        self.plot_tor.setYRange(-25, 25)
        self.plot_tor.showGrid(x=True, y=True, alpha=0.2)
        v2.addWidget(self.plot_tor, 1)

        self.plot_tor.addItem(pg.InfiniteLine(pos=0, angle=0, pen=pg.mkPen("w", width=1)))
        self.plot_tor.addItem(pg.InfiniteLine(pos=0, angle=90, pen=pg.mkPen("w", width=1)))

        self.line_t_live = self.plot_tor.plot([], [], pen=pg.mkPen("w", width=3))
        self.line_t_by_cond = {}
        for cond in CONDITION_DEFS:
            code = cond["code"]
            color = cond["color"]
            self.line_t_by_cond[code] = self.plot_tor.plot([], [], pen=pg.mkPen(color, width=3))

        legend_parts = ["Blanco: Live"]
        for cond in CONDITION_DEFS:
            legend_parts.append(f"{cond['short']}: {cond['label']}")
        self.lbl_tor_hint = QtWidgets.QLabel(" | ".join(legend_parts))
        v2.addWidget(self.lbl_tor_hint)

        self.tabs.addTab(self.tab_tor, "Torsión")

        # ---- Tab: Comparativo ----
        self.tab_cmp = QtWidgets.QWidget()
        self.tab_cmp = QtWidgets.QWidget()
        self.tabs.addTab(self.tab_cmp, "Comparativo")

        cmp_root = QtWidgets.QVBoxLayout(self.tab_cmp)
        cmp_root.setContentsMargins(0, 0, 0, 0)

        self.cmp_scroll = QtWidgets.QScrollArea()
        self.cmp_scroll.setWidgetResizable(True)
        cmp_root.addWidget(self.cmp_scroll, 1)

        # Contenido real scrolleable
        self.cmp_container = QtWidgets.QWidget()
        self.cmp_scroll.setWidget(self.cmp_container)

        v3 = QtWidgets.QVBoxLayout(self.cmp_container)
        v3.setContentsMargins(10, 10, 10, 10)
        v3.setSpacing(12)

        self.cmp_info = QtWidgets.QLabel(
            "Capturá condiciones o cargá sesiones para comparar. Arriba: superpuesto. Abajo: paneles separados.")
        v3.addWidget(self.cmp_info)

        # ===== Controles (check) =====
        ctrl = QtWidgets.QHBoxLayout()
        v3.addLayout(ctrl)

        self.cmp_checks = {}
        for cond in CONDITION_DEFS:
            chk = QtWidgets.QCheckBox(cond["short"])
            chk.setChecked(True)
            self.cmp_checks[cond["code"]] = chk

        self.chk_show_cop = QtWidgets.QCheckBox("COP")
        self.chk_show_tor = QtWidgets.QCheckBox("Torsión")
        self.chk_show_cop.setChecked(True)
        self.chk_show_tor.setChecked(True)

        for w in list(self.cmp_checks.values()) + [self.chk_show_cop, self.chk_show_tor]:
            w.stateChanged.connect(self.render_comparative)

        ctrl.addWidget(QtWidgets.QLabel("<b>Mostrar:</b>"))
        for chk in self.cmp_checks.values():
            ctrl.addWidget(chk)
        ctrl.addSpacing(20)
        ctrl.addWidget(self.chk_show_cop)
        ctrl.addWidget(self.chk_show_tor)
        self.btn_cmp_clear = QtWidgets.QPushButton("Limpiar comparativo")
        self.btn_cmp_clear.clicked.connect(self.clear_comparative)
        ctrl.addSpacing(12)
        ctrl.addWidget(self.btn_cmp_clear)
        ctrl.addStretch(1)

        # ===== Leyenda de colores =====
        legend_html = "  |  ".join(
            f'<span style="color:{cond["color_html"]};"><b>{cond["label"]}</b></span>'
            for cond in CONDITION_DEFS
        )
        self.lbl_cmp_legend = QtWidgets.QLabel(legend_html)
        v3.addWidget(self.lbl_cmp_legend)

        # ===== Plot SUPERPUESTO (arriba) =====
        self.plot_cmp_super = pg.PlotWidget()
        self.plot_cmp_super.setAspectLocked(True)
        self.plot_cmp_super.showGrid(x=True, y=True, alpha=0.2)
        self.plot_cmp_super.setXRange(X_MIN, X_MAX)
        self.plot_cmp_super.setYRange(Y_MIN, Y_MAX)
        self.plot_cmp_super.setMinimumHeight(320)
        v3.addWidget(self.plot_cmp_super, 2)

        # líneas centro
        self.plot_cmp_super.addItem(pg.InfiniteLine(pos=0, angle=0, pen=pg.mkPen("w", width=1)))
        self.plot_cmp_super.addItem(pg.InfiniteLine(pos=0, angle=90, pen=pg.mkPen("w", width=1)))

        # Items superpuestos (COP + torsión) por condición
        self.super_dots = {}
        self.super_t_lines = {}
        for cond in CONDITION_DEFS:
            code = cond["code"]
            color = cond["color"]
            dot = pg.ScatterPlotItem(size=20, brush=pg.mkBrush(color), pen=pg.mkPen(None))
            line = self.plot_cmp_super.plot([], [], pen=pg.mkPen(color, width=3))
            self.plot_cmp_super.addItem(dot)
            self.super_dots[code] = dot
            self.super_t_lines[code] = line

        self.plot_cmp_super.setMouseEnabled(False, False)
        self.plot_cmp_super.getViewBox().setMenuEnabled(False)

        # ===== Plot TRAZADOS COP (comparación) =====
        v3.addWidget(QtWidgets.QLabel("<b>Trazados COP (Izq / Global / Der)</b>"))

        self.plot_cmp_trails = pg.PlotWidget()
        self.plot_cmp_trails.setAspectLocked(True)
        self.plot_cmp_trails.showGrid(x=True, y=True, alpha=0.2)
        self.plot_cmp_trails.setXRange(-CMP_TRAIL_X_RANGE, CMP_TRAIL_X_RANGE)
        self.plot_cmp_trails.setYRange(-CMP_TRAIL_Y_RANGE, CMP_TRAIL_Y_RANGE)
        self.plot_cmp_trails.setMinimumHeight(400)
        v3.addWidget(self.plot_cmp_trails, 2)

        self.plot_cmp_trails.setMouseEnabled(False, False)
        self.plot_cmp_trails.getViewBox().setMenuEnabled(False)

        # líneas separadoras verticales (3 paneles)
        for x in [
            (CMP_PANEL_OFFSETS["L"] + CMP_PANEL_OFFSETS["G"]) / 2.0,
            (CMP_PANEL_OFFSETS["G"] + CMP_PANEL_OFFSETS["R"]) / 2.0,
        ]:
            self.plot_cmp_trails.addItem(pg.InfiniteLine(pos=x, angle=90, pen=pg.mkPen(120, 120, 120)))

        # línea central horizontal y vertical por panel (para referencia)
        self.plot_cmp_trails.addItem(pg.InfiniteLine(pos=0, angle=0, pen=pg.mkPen("w", width=1)))

        # títulos paneles
        for label, cx in [("Foot support (L)", CMP_PANEL_OFFSETS["L"]),
                          ("Barycenter (G)", CMP_PANEL_OFFSETS["G"]),
                          ("Foot support (R)", CMP_PANEL_OFFSETS["R"])]:
            ti = pg.TextItem(label, anchor=(0.5, 0), color="w")
            ti.setPos(cx, CMP_TRAIL_Y_RANGE - 1)
            self.plot_cmp_trails.addItem(ti)

        # Curvas: global / izq / der, por condición
        # Colores definidos en CONDITION_DEFS
        self.tr_cmp = {}
        for cond in CONDITION_DEFS:
            code = cond["code"]
            color = cond["color"]
            self.tr_cmp[code] = {
                "L": self.plot_cmp_trails.plot([], [], pen=pg.mkPen(color, width=2)),
                "G": self.plot_cmp_trails.plot([], [], pen=pg.mkPen(color, width=3)),
                "R": self.plot_cmp_trails.plot([], [], pen=pg.mkPen(color, width=2)),
            }

        # ===== Separador visual =====
        v3.addWidget(QtWidgets.QLabel("<hr>"))

        # ===== Plot PANEL (abajo, como ya tenías) =====
        self.plot_cmp = pg.PlotWidget()
        self.plot_cmp.setAspectLocked(True)
        self.plot_cmp.showGrid(x=True, y=True, alpha=0.2)
        self.plot_cmp.setXRange(-70, 70)
        self.plot_cmp.setYRange(-20, 40)
        self.plot_cmp.setMinimumHeight(600)
        v3.addWidget(self.plot_cmp, 3)

        self.plot_cmp.setMouseEnabled(False, False)
        self.plot_cmp.getViewBox().setMenuEnabled(False)

        self.tabs.addTab(self.tab_cmp, "Comparativo")

        # ---- Tab: Replay ----
        self.tab_rep = QtWidgets.QWidget()
        v4 = QtWidgets.QVBoxLayout(self.tab_rep)

        self.rep_info = QtWidgets.QLabel("Seleccioná una sesión y tocá Replay.")
        v4.addWidget(self.rep_info)

        # ===== Controles Replay =====
        rep_ctrl = QtWidgets.QHBoxLayout()
        v4.addLayout(rep_ctrl)

        self.btn_rep_play = QtWidgets.QPushButton("Play")
        self.btn_rep_play.setEnabled(False)
        self.btn_rep_play.clicked.connect(self.replay_toggle_play)
        rep_ctrl.addWidget(self.btn_rep_play)

        self.btn_rep_stop = QtWidgets.QPushButton("Stop")
        self.btn_rep_stop.setEnabled(False)
        self.btn_rep_stop.clicked.connect(self.replay_stop)
        rep_ctrl.addWidget(self.btn_rep_stop)

        rep_ctrl.addWidget(QtWidgets.QLabel("Velocidad:"))
        self.combo_rep_speed = QtWidgets.QComboBox()
        self.combo_rep_speed.addItems(["0.5x", "1x", "2x", "4x"])
        self.combo_rep_speed.setCurrentText("1x")
        self.combo_rep_speed.currentTextChanged.connect(self.replay_speed_changed)
        rep_ctrl.addWidget(self.combo_rep_speed)

        self.chk_rep_trail = QtWidgets.QCheckBox("Trayectoria")
        self.chk_rep_trail.setChecked(True)
        self.chk_rep_trail.stateChanged.connect(self.replay_redraw_trail)
        rep_ctrl.addWidget(self.chk_rep_trail)

        rep_ctrl.addStretch(1)

        # Slider tiempo
        self.rep_slider = QtWidgets.QSlider(QtCore.Qt.Horizontal)
        self.rep_slider.setEnabled(False)
        self.rep_slider.valueChanged.connect(self.replay_slider_changed)
        v4.addWidget(self.rep_slider)

        self.rep_time_lbl = QtWidgets.QLabel("t = 0.00 s")
        v4.addWidget(self.rep_time_lbl)

        self.btn_del_session = QtWidgets.QPushButton("Borrar grabación")
        self.btn_del_session.clicked.connect(self.delete_selected_session)
        left.addWidget(self.btn_del_session)

        # ===== Plot ANIMADO (arriba) =====
        self.rep_plot = pg.PlotWidget()
        self.rep_plot.setXRange(X_MIN, X_MAX)
        self.rep_plot.setYRange(Y_MIN, Y_MAX)
        self.rep_plot.showGrid(x=True, y=True, alpha=0.2)
        self.rep_plot.addItem(pg.InfiniteLine(pos=0, angle=0, pen=pg.mkPen("w", width=1)))
        self.rep_plot.addItem(pg.InfiniteLine(pos=0, angle=90, pen=pg.mkPen("w", width=1)))
        v4.addWidget(self.rep_plot, 3)

        # COP animado: global + pies (B)
        self.rep_dot_g = pg.ScatterPlotItem(size=COP_DOT_SIZE_G, brush=pg.mkBrush("r"), pen=pg.mkPen(None))
        self.rep_dot_l = pg.ScatterPlotItem(size=COP_DOT_SIZE_F, brush=pg.mkBrush("c"), pen=pg.mkPen(None))
        self.rep_dot_r = pg.ScatterPlotItem(size=COP_DOT_SIZE_F, brush=pg.mkBrush("g"), pen=pg.mkPen(None))
        self.rep_plot.addItem(self.rep_dot_g)
        self.rep_plot.addItem(self.rep_dot_l)
        self.rep_plot.addItem(self.rep_dot_r)

        # trayectoria (global)
        self.rep_traj_curve = self.rep_plot.plot([], [], pen=pg.mkPen("r", width=2))
        self.rep_traj_curve_l = self.rep_plot.plot([], [], pen=pg.mkPen("c", width=1))
        self.rep_traj_curve_r = self.rep_plot.plot([], [], pen=pg.mkPen("g", width=1))

        # torsión animada (línea blanca)
        self.rep_tor_line = self.rep_plot.plot([], [], pen=pg.mkPen("w", width=3))

        # ===== Síntesis ESTÁTICA (abajo) =====
        v4.addWidget(QtWidgets.QLabel("<hr><b>Síntesis (estática)</b>"))

        self.rep_plot_static = pg.PlotWidget()
        self.rep_plot_static.setXRange(X_MIN, X_MAX)
        self.rep_plot_static.setYRange(Y_MIN, Y_MAX)
        self.rep_plot_static.showGrid(x=True, y=True, alpha=0.2)
        self.rep_plot_static.addItem(pg.InfiniteLine(pos=0, angle=0, pen=pg.mkPen("w", width=1)))
        self.rep_plot_static.addItem(pg.InfiniteLine(pos=0, angle=90, pen=pg.mkPen("w", width=1)))
        v4.addWidget(self.rep_plot_static, 2)

        self.rep_static_dot = pg.ScatterPlotItem(size=COP_DOT_SIZE_G, brush=pg.mkBrush("r"), pen=pg.mkPen(None))
        self.rep_plot_static.addItem(self.rep_static_dot)
        self.rep_static_tor = self.rep_plot_static.plot([], [], pen=pg.mkPen("w", width=3))

        self.tabs.addTab(self.tab_rep, "Replay")

    def _init_kapandji_overlay(self):
        self.kap_pos = {
            "L_med": (-5.5,  7.0),
            "L_lat": (-10.5,  2.0),
            "L_heel": (-7.5, -8.0),
            "R_med": ( 5.5,  7.0),
            "R_lat": (10.5,  2.0),
            "R_heel": ( 7.5, -8.0),
        }
        for _ in range(6):
            it = pg.ScatterPlotItem(size=KAP_DOT_SIZE, brush=pg.mkBrush(60, 200, 90), pen=pg.mkPen("w"))
            self.plot_live.addItem(it)
            self.kap_items.append(it)
        for _ in range(6):
            ti = pg.TextItem("", anchor=(0.5, -0.6), color="w")
            self.plot_live.addItem(ti)
            self.kap_text_items.append(ti)

    def toggle_sidebar(self):
        if not hasattr(self, "splitter"):
            return

        sizes = self.splitter.sizes()
        left_w = sizes[0]
        total = max(1, sum(sizes))

        # colapsar
        if left_w > 20:
            self._sidebar_prev_w = left_w
            self.splitter.setSizes([0, total])
            self.btn_toggle_sidebar.setText("⟩⟩")
        else:
            w = getattr(self, "_sidebar_prev_w", 320)
            self.splitter.setSizes([w, max(200, total - w)])
            self.btn_toggle_sidebar.setText("⟨⟨")

    # ---------- Patients ----------
    def _load_patients(self):
        self.list_patients.clear()
        self.patients = db_list_patients(self.con)
        for pid, name, dob, created_at in self.patients:
            self.list_patients.addItem(name)

    def on_patient_selected(self, idx: int):
        if idx < 0 or idx >= len(self.patients):
            self.current_patient = None
            self.list_sessions.clear()
            self.lbl_patient_info.setText("Nacimiento: -- | Edad: --")
            return
        pid, name, dob_iso, _ = self.patients[idx]
        self.current_patient = (pid, name, dob_iso)
        dob_date = date.fromisoformat(dob_iso) if dob_iso else None
        edad = age_years(dob_date) if dob_date else None
        self.lbl_patient_info.setText(
            f"Nacimiento: {dob_iso if dob_iso else '--'} | Edad: {edad if edad is not None else '--'}"
        )
        self.refresh_sessions()

    def add_patient(self):
        dlg = AddPatientDialog(self)
        try:
            if dlg.exec() == QtWidgets.QDialog.Accepted:
                name, dob_iso = dlg.values()
                db_add_patient(self.con, name, dob_iso)
                self._load_patients()
        except Exception as e:
            QtWidgets.QMessageBox.warning(self, "Error", str(e))

    def delete_patient(self):
        idx = self.list_patients.currentRow()
        if idx < 0 or idx >= len(self.patients):
            return
        pid, name, dob, _ = self.patients[idx]
        resp = QtWidgets.QMessageBox.question(
            self, "Confirmar",
            f"¿Eliminar el paciente '{name}'?",
            QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No
        )
        if resp == QtWidgets.QMessageBox.Yes:
            db_delete_patient(self.con, pid)
            self._load_patients()
            self.list_sessions.clear()
            self.current_patient = None

    # ---------- Sessions ----------
    def patient_folder(self, patient_name: str) -> str:
        return os.path.join(PATIENTS_DIR, slugify(patient_name))

    def refresh_sessions(self):
        self.list_sessions.clear()

        if not self.current_patient:
            return

        _, pname, _ = self.current_patient
        patient_dir = self.patient_folder(pname)

        if not os.path.isdir(patient_dir):
            return

        session_folders = [d for d in os.listdir(patient_dir) if os.path.isdir(os.path.join(patient_dir, d))]
        session_folders.sort(reverse=True)

        for folder in session_folders:
            meta_path = os.path.join(patient_dir, folder, "meta.json")
            cond = "?"
            date_str = folder  # fallback
            display_name = folder

            if os.path.isfile(meta_path):
                try:
                    with open(meta_path, "r", encoding="utf-8") as f:
                        meta = json.load(f)
                    cond = normalize_condition(meta.get("condition", "?"))
                    created_at = meta.get("created_at", "")
                    # created_at: "2026-01-17T16:10:05"
                    if "T" in created_at:
                        date_str = created_at.replace("T", " ")
                    display_name = meta.get("session_name", folder)
                except:
                    pass

            label = f"{display_name}  |  {date_str}  |  {cond}"
            it = QtWidgets.QListWidgetItem(label)
            # IMPORTANTÍSIMO: guardamos el nombre real de la carpeta para abrir session.csv después
            it.setData(QtCore.Qt.UserRole, folder)
            self.list_sessions.addItem(it)

    # ---------- COM ports / Autodetect ----------
    def refresh_com_ports(self):
        self.combo_com.clear()
        ports = list(serial.tools.list_ports.comports())
        if not ports:
            self.combo_com.addItem("Sin puertos")
            return

        # ordenamos por score para mostrar lo “probable” arriba
        ports_sorted = sorted(ports, key=port_score, reverse=True)
        for p in ports_sorted:
            label = f"{p.device}  |  {p.description or ''}"
            if p.vid is not None and p.pid is not None:
                label += f"  |  VID:PID {p.vid:04X}:{p.pid:04X}"
            self.combo_com.addItem(label, p.device)

        # preseleccionar el mejor
        best = pick_best_port(ports_sorted)
        if best:
            for i in range(self.combo_com.count()):
                dev = self.combo_com.itemData(i)
                if dev == best:
                    self.combo_com.setCurrentIndex(i)
                    break

    def auto_connect(self):
        if self.serial_ok:
            return
        # intenta conectar al puerto seleccionado (que ya es el “mejor”)
        if self.combo_com.currentText() == "Sin puertos":
            return
        self.toggle_connection()

    # ---------- Connect/Disconnect ----------
    def set_status_connected(self, port: str):
        self.lbl_serial.setText(f"Posturómetro conectado ({port})")
        self.lbl_serial.setStyleSheet("color: green; font-weight: bold;")
        self.btn_connect.setText("Desconectar")

    def set_status_disconnected(self):
        self.lbl_serial.setText("Posturómetro desconectado")
        self.lbl_serial.setStyleSheet("color: red; font-weight: bold;")
        self.btn_connect.setText("Conectar")

    def toggle_connection(self):
        if self.serial_ok:
            # DESCONECTAR
            try:
                if self.ser and self.ser.is_open:
                    self.ser.close()
            except:
                pass
            self.ser = None
            self.serial_ok = False
            self.current_port = None
            self.set_status_disconnected()
            self.statusBar().showMessage("Desconectado.")
            return

        # CONECTAR
        if self.combo_com.currentText() == "Sin puertos":
            QtWidgets.QMessageBox.warning(self, "COM", "No hay puertos disponibles.")
            return

        port = self.combo_com.currentData()
        if not port:
            # fallback: si no hay itemData
            port = self.combo_com.currentText().split("|")[0].strip()

        try:
            self.ser = serial.Serial(port, BAUD, timeout=0)
            time.sleep(2)
            self.ser.reset_input_buffer()

            self.serial_ok = True
            self.current_port = port
            self.set_status_connected(port)
            self.statusBar().showMessage("Conectado y leyendo datos.")

        except Exception as e:
            self.serial_ok = False
            self.current_port = None
            self.set_status_disconnected()
            QtWidgets.QMessageBox.critical(self, "Error de conexión", str(e))

    # ---------- Serial read ----------
    def read_last_valid_frame(self):
        if not self.serial_ok or not self.ser:
            return None
        last = None
        while self.ser.in_waiting:
            try:
                raw = self.ser.readline().decode(errors="ignore").strip()
                parts = raw.split(",")
                if len(parts) == FRAME_LEN:
                    last = list(map(float, parts))
            except:
                pass
        return last

    # ---------- Recording ----------
    def start_new_session(self):
        if not self.current_patient:
            QtWidgets.QMessageBox.information(self, "Paciente", "Elegí o creá un paciente primero.")
            return
        if self.recording:
            QtWidgets.QMessageBox.information(self, "Grabación", "Ya estás grabando. Primero STOP.")
            return
        if not self.serial_ok:
            QtWidgets.QMessageBox.information(self, "Conexión", "Conectá el posturómetro antes de grabar.")
            return

        _, pname, dob_iso = self.current_patient
        dlg = NewSessionDialog(pname, self)
        if dlg.exec() != QtWidgets.QDialog.Accepted:
            return

        sess_name = dlg.session_name().strip()
        if not sess_name:
            QtWidgets.QMessageBox.warning(self, "Sesión", "Nombre de sesión inválido.")
            return

        folder = slugify(sess_name)
        self.session_condition = normalize_condition(dlg.condition())

        if dlg.clear_trails():
            self.clear_all()

        # ===== crear carpeta de sesión =====
        session_dir = os.path.join(self.patient_folder(pname), folder)
        os.makedirs(session_dir, exist_ok=True)
        self.current_session_dir = session_dir

        # ===== CSV =====
        csv_path = os.path.join(session_dir, "session.csv")
        self.csv_file = open(csv_path, "w", newline="", encoding="utf-8")
        self.csv_writer = csv.writer(self.csv_file)
        self.csv_writer.writerow([
            "timestamp",
            "p0", "p1", "p2", "p3", "p4", "p5",
            "xg", "yg", "xl", "yl", "xr", "yr",
            "PL", "PR",
            "overload", "torsion_deg",
            "sway_path", "mean_speed", "rms_x", "rms_y",
            "condition"
        ])

        # ===== META =====
        meta = {
            "patient": pname,
            "dob": dob_iso,
            "condition": self.session_condition,
            "session_name": sess_name,
            "created_at": datetime.now().isoformat(timespec="seconds"),
            "port": self.current_port,
            "baud": BAUD,
            "ema_alpha": EMA_ALPHA,
            "metric_window_frames": METRIC_WINDOW
        }
        with open(os.path.join(session_dir, "meta.json"), "w", encoding="utf-8") as f:
            json.dump(meta, f, indent=2, ensure_ascii=False)

        # ===== ESTADO =====
        self.recording = True
        if hasattr(self, "lbl_rec"):
            self.lbl_rec.setVisible(True)
        self.btn_stop.setEnabled(True)
        self.btn_new_session.setEnabled(False)
        self.statusBar().showMessage(f"Grabando: {sess_name} ({self.session_condition})")

        self.refresh_sessions()

    def stop_recording(self):
        if not self.recording:
            return
        self.recording = False
        if hasattr(self, "lbl_rec"):
            self.lbl_rec.setVisible(False)
        self.btn_stop.setEnabled(False)
        self.btn_new_session.setEnabled(True)
        try:
            if self.csv_file:
                self.csv_file.flush()
                self.csv_file.close()
        except:
            pass
        self.csv_file = None
        self.csv_writer = None
        self.current_session_dir = None
        self.statusBar().showMessage("Grabación detenida.")

    # ---------- Pause / Clear ----------
    def toggle_pause(self):
        self.paused = self.btn_pause.isChecked()
        self.btn_pause.setText("REANUDAR" if self.paused else "PAUSA")
        self.statusBar().showMessage("PAUSADO (freeze)." if self.paused else "LIVE.")

    def clear_all(self):
        self.trail_g.clear()
        self.trail_l.clear()
        self.trail_r.clear()
        self.metric_win = MetricWindow(maxlen=METRIC_WINDOW)
        self.recent.clear()
        self.last_processed = None
        self.statusBar().showMessage("Limpio (trayectorias y métricas).")

    def clear_comparative(self):
        for code in CONDITION_CODES:
            self.snapshots[code] = None
        self.cmp_trails = {}
        self.render_comparative()

    # ---------- Kapandji / Torsión helpers ----------
    def compute_kapandji_loads(self, p0, p1, p2, p3, p4, p5):
        # Mapeo funcional Kapandji (TOP/SIDE/HEEL):
        # Izq: TOP=p0, SIDE=p1, HEEL=p2
        # Der: TOP=p5, SIDE=p4, HEEL=p3
        # TOP   -> medial anterior (1° metatarsiano) baseline 2/6
        # SIDE  -> lateral anterior (5° metatarsiano) baseline 1/6
        # HEEL  -> posterior calcáneo (talón) baseline 3/6

        L_top = p0
        L_side = p1
        L_heel = p2

        R_top = p5
        R_side = p4
        R_heel = p3

        # devolvemos cargas absolutas por zona (unidades crudas calibradas)
        kapL = (L_top, L_side, L_heel)
        kapR = (R_top, R_side, R_heel)
        return kapL, kapR


    def update_kapandji_overlay(self, kapL, kapR, PT=0.0):
        # kapL/kapR: (forefoot, lateral, heel)
        vals = [kapL[0], kapL[1], kapL[2], kapR[0], kapR[1], kapR[2]]
        keys = ["L_med", "L_lat", "L_heel", "R_med", "R_lat", "R_heel"]
        PL = kapL[0] + kapL[1] + kapL[2]
        PR = kapR[0] + kapR[1] + kapR[2]
        no_support = PT <= KAP_NO_SUPPORT_PT
        for i, key in enumerate(keys):
            x, y = self.kap_pos[key]
            value = vals[i]
            if no_support:
                r, g, b = KAP_COLOR_NEUTRAL
            else:
                r, g, b = kap_color_by_point(key, value, PL, PR)
            self.kap_items[i].setData([x], [y])
            self.kap_items[i].setBrush(pg.mkBrush(r, g, b))
            self.kap_items[i].setPen(pg.mkPen("w"))
            self.kap_text_items[i].setText(kap_point_label(key, value, PL, PR))
            self.kap_text_items[i].setPos(x, y)

    def torsion_deg_from_feet(self, xl, yl, xr, yr):
        deg = math.degrees(math.atan2((yr - yl), (xr - xl)))
        if INVERT_TORSION_SIGN:
            deg = -deg
        return deg

    def segment_for_angle(self, deg: float, length: float = 40.0):
        th = math.radians(deg)
        dx = (length/2.0)*math.cos(th)
        dy = (length/2.0)*math.sin(th)
        return ([-dx, dx], [-dy, dy])

    # ---------- Snapshots / Comparativo ----------
    def capture_condition(self, cond: str):
        if len(self.recent) < 30:
            QtWidgets.QMessageBox.information(self, "Captura", "Todavía no hay suficientes datos para capturar.")
            return
        recent = list(self.recent)

        def median(vals):
            s = sorted(vals)
            n = len(s)
            if n == 0:
                return 0.0
            if n % 2 == 1:
                return s[n//2]
            return 0.5*(s[n//2 - 1] + s[n//2])

        snap = {}
        for k in ["xg","yg","xl","yl","xr","yr","PL","PR","overload","torsion_deg"]:
            snap[k] = median([d[k] for d in recent])
        for k in ["L_med","L_lat","L_heel","R_med","R_lat","R_heel"]:
            snap[k] = median([d[k] for d in recent])
        snap["cond"] = cond
        snap["ts"] = datetime.now().isoformat(timespec="seconds")
        self.snapshots[cond] = snap
        self.statusBar().showMessage(f"Capturado {cond} (estabilizado).")
        self.render_comparative()

    def _condition_panel_positions(self):
        count = len(CONDITION_DEFS)
        if count <= 1:
            return {CONDITION_DEFS[0]["code"]: 0.0} if count == 1 else {}
        start = -60.0
        end = 60.0
        step = (end - start) / (count - 1)
        return {cond["code"]: start + idx * step for idx, cond in enumerate(CONDITION_DEFS)}

    def render_comparative(self):
        # Trazados COP comparativos: si no están inicializados, igual dibujamos el resto
        has_trails = hasattr(self, "tr_cmp") and all(k in self.tr_cmp for k in CONDITION_CODES)

        # -------- SUPERPUESTO (arriba) --------
        def show_cond(cond: str) -> bool:
            chk = self.cmp_checks.get(cond)
            return chk.isChecked() if chk else True

        show_cop = self.chk_show_cop.isChecked()
        show_tor = self.chk_show_tor.isChecked()

        # helper para poner/ocultar items
        def set_dot(dot_item, x, y, visible: bool):
            dot_item.setVisible(visible)
            if visible:
                dot_item.setData([x], [y])
            else:
                dot_item.setData([], [])

        def set_line(line_item, xs, ys, visible: bool):
            line_item.setVisible(visible)
            if visible:
                line_item.setData(xs, ys)
            else:
                line_item.setData([], [])

        # leer snapshots
        # COP superpuesto
        for cond in CONDITION_CODES:
            snap = self.snapshots.get(cond)
            dot = self.super_dots.get(cond)
            line = self.super_t_lines.get(cond)
            if not dot or not line:
                continue
            if snap:
                set_dot(dot, snap["xg"], snap["yg"], show_cond(cond) and show_cop)
                xs, ys = self.segment_for_angle(snap["torsion_deg"], length=20.0)
                set_line(line, xs, ys, show_cond(cond) and show_tor)
            else:
                set_dot(dot, 0, 0, False)
                set_line(line, [], [], False)

        # -------- PANEL (abajo) --------
        self.plot_cmp.clear()
        self.plot_cmp.showGrid(x=True, y=True, alpha=0.2)

        panel_positions = self._condition_panel_positions()
        positions = [panel_positions[c["code"]] for c in CONDITION_DEFS]
        for i in range(len(positions) - 1):
            mid = (positions[i] + positions[i + 1]) / 2.0
            self.plot_cmp.addItem(pg.InfiniteLine(pos=mid, angle=90, pen=pg.mkPen(120, 120, 120)))

        for cond in CONDITION_DEFS:
            label = cond["short"]
            cx = panel_positions[cond["code"]]
            ti = pg.TextItem(label, anchor=(0.5, 0), color="w")
            ti.setPos(cx, 35)
            self.plot_cmp.addItem(ti)

        def draw_panel(cond: str, cx: float, color_pen):
            if not show_cond(cond):
                ti = pg.TextItem("Oculto", anchor=(0.5, 0.5), color=(180, 180, 180))
                ti.setPos(cx, 10)
                self.plot_cmp.addItem(ti)
                return

            snap = self.snapshots.get(cond)
            if not snap:
                ti = pg.TextItem("Sin captura", anchor=(0.5, 0.5), color=(180, 180, 180))
                ti.setPos(cx, 10)
                self.plot_cmp.addItem(ti)
                return

            PL = snap["PL"];
            PR = snap["PR"]
            total = PL + PR
            overload = snap["overload"]
            left_pct = (100 * PL / total) if total > 0 else 0
            right_pct = (100 * PR / total) if total > 0 else 0

            if PL > PR:
                arrow = "←"
            elif PR > PL:
                arrow = "→"
            else:
                arrow = "↔"

            arrow_html = f'<span style="font-size:16pt;">{arrow}</span>'
            line1 = f"L {left_pct:0.1f}% | R {right_pct:0.1f}% {arrow_html}"
            line2 = f"Overload {overload:0.2f}"
            tinfo = pg.TextItem(anchor=(0.5, 1.0), color="w")
            tinfo.setHtml(f"{line1}<br>{line2}")
            tinfo.setPos(cx, -15)
            self.plot_cmp.addItem(tinfo)

            no_support = (PL + PR) <= KAP_NO_SUPPORT_PT

            pos = {
                "L_med": (cx - 6, 18), "L_lat": (cx - 11, 10), "L_heel": (cx - 8, 0),
                "R_med": (cx + 6, 18), "R_lat": (cx + 11, 10), "R_heel": (cx + 8, 0),
            }
            keys = ["L_med", "L_lat", "L_heel", "R_med", "R_lat", "R_heel"]
            for k in keys:
                x, y = pos[k]
                value = snap[k]
                if no_support:
                    r, g, b = KAP_COLOR_NEUTRAL
                else:
                    r, g, b = kap_color_by_point(k, value, PL, PR)
                sc = pg.ScatterPlotItem(size=18, brush=pg.mkBrush(r, g, b), pen=pg.mkPen("w"))
                sc.setData([x], [y])
                self.plot_cmp.addItem(sc)
                tt = pg.TextItem(kap_point_label(k, value, PL, PR), anchor=(0.5, -0.6), color="w")
                tt.setPos(x, y)
                self.plot_cmp.addItem(tt)

            # torsión en panel
            xs, ys = self.segment_for_angle(snap["torsion_deg"], length=18.0)
            xs = [x + cx for x in xs]
            ys = [y + 25 for y in ys]
            self.plot_cmp.plot(xs, ys, pen=color_pen)

        for cond in CONDITION_DEFS:
            code = cond["code"]
            cx = panel_positions[code]
            draw_panel(code, cx, pg.mkPen(cond["color"], width=3))

        # -------- TRAZADOS COP (L / G / R) --------
        def _cond_visible(cond: str) -> bool:
            chk = self.cmp_checks.get(cond)
            return chk.isChecked() if chk else True

        # offset por panel (en X)
        panel_x = CMP_PANEL_OFFSETS

        def set_curve(curve, pts, xoff, visible=True):
            curve.setVisible(visible)
            if visible and pts:
                xs = [p[0] + xoff for p in pts]
                ys = [p[1] for p in pts]
                curve.setData(xs, ys)
            else:
                curve.setData([], [])

        # si no hay trazados inicializados, no hacemos nada en esta sección
        if not has_trails:
            return

        # si no hay trails cargados, vaciamos
        for cond in CONDITION_CODES:
            vis = _cond_visible(cond)
            tr = self.cmp_trails.get(cond)

            if not tr:
                for comp in ["L", "G", "R"]:
                    self.tr_cmp[cond][comp].setData([], [])
                continue

            set_curve(self.tr_cmp[cond]["L"], tr.get("L", []), panel_x["L"], visible=vis)
            set_curve(self.tr_cmp[cond]["G"], tr.get("G", []), panel_x["G"], visible=vis)
            set_curve(self.tr_cmp[cond]["R"], tr.get("R", []), panel_x["R"], visible=vis)

    # ---------- Replay (síntesis) ----------
    def replay_selected_session(self):
        if not self.current_patient:
            QtWidgets.QMessageBox.warning(self, "Replay", "Seleccioná un paciente primero.")
            return

        _, pname, _ = self.current_patient

        item = self.list_sessions.currentItem()
        if not item:
            return

        folder = item.data(QtCore.Qt.UserRole)
        if not folder:
            QtWidgets.QMessageBox.warning(self, "Replay", "Sesión inválida (no tiene carpeta asociada).")
            return

        session_dir = os.path.join(self.patient_folder(pname), folder)
        csv_path = os.path.join(session_dir, "session.csv")

        if not os.path.isfile(csv_path):
            QtWidgets.QMessageBox.warning(self, "Replay", f"No existe session.csv en:\n{session_dir}")
            return

        # ... desde acá seguís con tu lógica actual de replay (leer CSV, etc.)

        # ---- Leer CSV completo ----
        rows = []
        with open(csv_path, "r", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                rows.append(row)

        if not rows:
            QtWidgets.QMessageBox.warning(self, "Replay", "El CSV está vacío.")
            return

        def safe_float(x):
            try:
                return float(x)
            except:
                return None

        def get_any(rr, cols):
            for c in cols:
                if c in rr and rr[c] not in (None, "", "nan"):
                    v = safe_float(rr[c])
                    if v is not None:
                        return v
            return None

        # Arrays (B: global + L/R + torsión)
        ts = []
        xgA = [];
        ygA = []
        xlA = [];
        ylA = []
        xrA = [];
        yrA = []
        torA = []

        # Si el CSV no tiene torsion_deg, la calculamos desde (xl,yl,xr,yr)
        for rr in rows:
            t = get_any(rr, ["timestamp", "t", "time"])
            xg = get_any(rr, ["xg", "xG", "xG_ema"])
            yg = get_any(rr, ["yg", "yG", "yG_ema"])
            xl = get_any(rr, ["xl", "copXL", "xL"])
            yl = get_any(rr, ["yl", "copYL", "yL"])
            xr = get_any(rr, ["xr", "copXR", "xR"])
            yr = get_any(rr, ["yr", "copYR", "yR"])
            tor = get_any(rr, ["torsion_deg", "torsion", "torsionAngle"])

            # si faltan datos mínimos, saltamos la fila
            if t is None or xg is None or yg is None:
                continue

            # si no hay pies en CSV viejo, al menos no rompemos:
            if xl is None: xl = 0.0
            if yl is None: yl = 0.0
            if xr is None: xr = 0.0
            if yr is None: yr = 0.0

            if tor is None:
                # torsión desde pies
                tor = math.degrees(math.atan2((yr - yl), (xr - xl))) if (xl or yl or xr or yr) else 0.0

            ts.append(t)
            xgA.append(xg);
            ygA.append(yg)
            xlA.append(xl);
            ylA.append(yl)
            xrA.append(xr);
            yrA.append(yr)
            torA.append(tor)

        if len(ts) < 2:
            QtWidgets.QMessageBox.warning(self, "Replay", "No hay suficientes muestras para reproducir.")
            return

        # Normalizar tiempo a segundos desde inicio
        t0 = ts[0]
        tsec = [tt - t0 for tt in ts]

        # Guardar en estado replay
        self.replay_data = {
            "name": item.text(),
            "t": tsec,
            "xg": xgA, "yg": ygA,
            "xl": xlA, "yl": ylA,
            "xr": xrA, "yr": yrA,
            "tor": torA,
        }
        self.replay_idx = 0
        self.replay_playing = False

        # Preparar slider
        self.rep_slider.blockSignals(True)
        self.rep_slider.setEnabled(True)
        self.rep_slider.setMinimum(0)
        self.rep_slider.setMaximum(len(tsec) - 1)
        self.rep_slider.setValue(0)
        self.rep_slider.blockSignals(False)

        # Habilitar botones
        self.btn_rep_play.setEnabled(True)
        self.btn_rep_stop.setEnabled(True)
        self.btn_rep_play.setText("Play")

        # Dibujar primer frame animado
        self.replay_draw_index(0)

        # ---- Síntesis estática (mediana) ----
        def median(vals):
            s = sorted(vals)
            n = len(s)
            return s[n // 2] if n % 2 == 1 else 0.5 * (s[n // 2 - 1] + s[n // 2])

        xg_med = median(xgA)
        yg_med = median(ygA)
        tor_med = median(torA)

        self.rep_static_dot.setData([xg_med], [yg_med])
        xs, ys = self.segment_for_angle(tor_med, length=20.0)
        self.rep_static_tor.setData(xs, ys)

        self.rep_info.setText(f"Replay: {item.text()} | muestras: {len(tsec)} | duración: {tsec[-1]:.1f}s")
        self.tabs.setCurrentWidget(self.tab_rep)

        # --- helpers ROBUSTOS (van acá) ---
        def safe_median(vals):
            vals = [v for v in vals if v is not None]
            if not vals:
                return 0.0
            s = sorted(vals)
            n = len(s)
            return s[n // 2] if n % 2 == 1 else 0.5 * (s[n // 2 - 1] + s[n // 2])

        def get_float_any(cols):
            out = []
            for rr in rows:
                for c in cols:
                    if c in rr and rr[c] not in (None, "", "nan"):
                        try:
                            out.append(float(rr[c]))
                            break
                        except:
                            pass
            return out

        xg = safe_median(get_float_any(["xg", "xG", "xG_ema"]))
        yg = safe_median(get_float_any(["yg", "yG", "yG_ema"]))

        overload = safe_median(get_float_any(["overload", "Overload"]))

        torsion_deg = safe_median(get_float_any(["torsion_deg", "torsion", "torsionAngle"]))

        # Si no existe torsion_deg en CSV viejo, la calculamos desde COP pies si están
        if torsion_deg == 0.0:
            xl = safe_median(get_float_any(["xl", "copXL", "xL"]))
            yl = safe_median(get_float_any(["yl", "copYL", "yL"]))
            xr = safe_median(get_float_any(["xr", "copXR", "xR"]))
            yr = safe_median(get_float_any(["yr", "copYR", "yR"]))
            if (xl != 0.0 or yl != 0.0 or xr != 0.0 or yr != 0.0):
                torsion_deg = math.degrees(math.atan2((yr - yl), (xr - xl)))

        cond = rows[-1].get("condition", rows[-1].get("Condicion", "NO"))

        self.rep_plot.setXRange(X_MIN, X_MAX)
        self.rep_plot.setYRange(Y_MIN, Y_MAX)
        self.rep_dot.setData([xg],[yg])

        xs, ys = self.segment_for_angle(torsion_deg, length=20.0)
        self.rep_tor_line.setData(xs, ys)

        self.rep_info.setText(
            f"Replay síntesis: {item.text()} | condición: {cond} | overload: {overload:0.2f} | torsión: {torsion_deg:+0.2f}°"
        )
        self.tabs.setCurrentWidget(self.tab_rep)

    def _load_trails_and_snapshot(self, csv_path: str):
        rows = []
        with open(csv_path, "r", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for rr in r:
                rows.append(rr)

        if not rows:
            return None, None

        def fget(rr, keys):
            for k in keys:
                if k in rr and rr[k] not in ("", None, "nan"):
                    try:
                        return float(rr[k])
                    except:
                        pass
            return None

        # trails
        L = []
        G = []
        R = []
        PLs = []
        PRs = []
        tors = []
        kap = {"L_med": [], "L_lat": [], "L_heel": [], "R_med": [], "R_lat": [], "R_heel": []}

        for rr in rows:
            xg = fget(rr, ["xg", "xG", "xG_ema"]);
            yg = fget(rr, ["yg", "yG", "yG_ema"])
            xl = fget(rr, ["xl", "copXL", "xL"]);
            yl = fget(rr, ["yl", "copYL", "yL"])
            xr = fget(rr, ["xr", "copXR", "xR"]);
            yr = fget(rr, ["yr", "copYR", "yR"])
            PL = fget(rr, ["PL"]);
            PR = fget(rr, ["PR"])
            tor = fget(rr, ["torsion_deg", "torsion", "torsionAngle"])
            p0 = fget(rr, ["p0"]);
            p1 = fget(rr, ["p1"]);
            p2 = fget(rr, ["p2"])
            p3 = fget(rr, ["p3"]);
            p4 = fget(rr, ["p4"]);
            p5 = fget(rr, ["p5"])

            if xg is None or yg is None:
                continue

            G.append((xg, yg))
            if xl is not None and yl is not None:
                L.append((xl, yl))
            if xr is not None and yr is not None:
                R.append((xr, yr))

            if PL is not None: PLs.append(PL)
            if PR is not None: PRs.append(PR)

            if tor is None and xl is not None and yl is not None and xr is not None and yr is not None:
                tor = math.degrees(math.atan2((yr - yl), (xr - xl)))
            if tor is not None:
                tors.append(tor)

            has_raw_kap = False
            if None not in (p0, p1, p2, p3, p4, p5):
                kapL, kapR = self.compute_kapandji_loads(p0, p1, p2, p3, p4, p5)
                # kapL y kapR son cargas absolutas [med, lat, heel]
                kap["L_med"].append(kapL[0]);
                kap["L_lat"].append(kapL[1]);
                kap["L_heel"].append(kapL[2])
                kap["R_med"].append(kapR[0]);
                kap["R_lat"].append(kapR[1]);
                kap["R_heel"].append(kapR[2])
                has_raw_kap = True

            # Fallback para CSV viejos sin p0..p5: tomar columnas Kapandji si existen
            if not has_raw_kap:
                for k in kap.keys():
                    v = fget(rr, [k])
                    if v is not None:
                        kap[k].append(v)

        def med(vals):
            if not vals:
                return 0.0
            s = sorted(vals);
            n = len(s)
            return s[n // 2] if n % 2 == 1 else 0.5 * (s[n // 2 - 1] + s[n // 2])

        PLm = med(PLs);
        PRm = med(PRs)
        total = PLm + PRm
        overload = abs(PLm - PRm) / total if total > 1e-9 else 0.0

        snap = {
            "xg": med([p[0] for p in G]) if G else 0.0,
            "yg": med([p[1] for p in G]) if G else 0.0,
            "PL": PLm,
            "PR": PRm,
            "overload": overload,
            "torsion_deg": med(tors),
            "L_med": med(kap["L_med"]), "L_lat": med(kap["L_lat"]), "L_heel": med(kap["L_heel"]),
            "R_med": med(kap["R_med"]), "R_lat": med(kap["R_lat"]), "R_heel": med(kap["R_heel"]),
        }

        trails = {"L": L, "G": G, "R": R}
        return snap, trails

    def compare_from_selected_sessions(self):
        if not self.current_patient:
            QtWidgets.QMessageBox.warning(self, "Comparativo", "Seleccioná un paciente primero.")
            return

        items = self.list_sessions.selectedItems()
        if len(items) < 2 or len(items) > 5:
            QtWidgets.QMessageBox.warning(self, "Comparativo", "Seleccioná entre 2 y 5 sesiones.")
            return

        _, pname, _ = self.current_patient
        base_dir = self.patient_folder(pname)

        # ---- construir lista de sesiones seleccionadas ----
        sessions = []
        for it in items:
            folder = it.data(QtCore.Qt.UserRole)
            if not folder:
                QtWidgets.QMessageBox.warning(self, "Comparativo", "Sesión inválida (sin carpeta UserRole).")
                return

            session_dir = os.path.join(base_dir, folder)
            csv_path = os.path.join(session_dir, "session.csv")
            meta_path = os.path.join(session_dir, "meta.json")

            if not os.path.isfile(csv_path):
                QtWidgets.QMessageBox.warning(self, "Comparativo", f"No existe session.csv en:\n{session_dir}")
                return

            cond = None
            if os.path.isfile(meta_path):
                try:
                    with open(meta_path, "r", encoding="utf-8") as f:
                        meta = json.load(f)
                    cond = normalize_condition(meta.get("condition", None))
                except:
                    cond = None

            sessions.append({
                "label": it.text(),  # lo que ve el usuario
                "folder": folder,  # carpeta real
                "csv_path": csv_path,
                "cond": cond  # condición normalizada o None
            })

        # ---- 1) mapear por meta.json si se puede ----
        mapping = {}
        needs_manual = False
        for s in sessions:
            if s["cond"] in CONDITION_CODES and s["cond"] not in mapping:
                mapping[s["cond"]] = s
            else:
                needs_manual = True

        # ---- 2) si falta algo o hay duplicados, pedir asignación manual ----
        if needs_manual or len(mapping) != len(sessions):
            dlg = QtWidgets.QDialog(self)
            dlg.setWindowTitle("Asignar condiciones a sesiones")
            lay = QtWidgets.QVBoxLayout(dlg)

            lay.addWidget(QtWidgets.QLabel(
                "Asigná una condición distinta a cada sesión seleccionada:"
            ))

            condition_labels = [c["label"] for c in CONDITION_DEFS]
            label_to_code = {c["label"]: c["code"] for c in CONDITION_DEFS}
            rows = []
            for s in sessions:
                row = QtWidgets.QHBoxLayout()
                row.addWidget(QtWidgets.QLabel(s["label"]))
                combo = QtWidgets.QComboBox()
                combo.addItems(condition_labels)
                if s["cond"] in CONDITION_BY_CODE:
                    combo.setCurrentText(CONDITION_BY_CODE[s["cond"]]["label"])
                row.addWidget(combo, 1)
                lay.addLayout(row)
                rows.append((s, combo))

            btns = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel)
            lay.addWidget(btns)
            btns.accepted.connect(dlg.accept)
            btns.rejected.connect(dlg.reject)

            if dlg.exec() != QtWidgets.QDialog.Accepted:
                return

            picked_codes = []
            for s, combo in rows:
                code = label_to_code.get(combo.currentText())
                picked_codes.append(code)

            if any(code is None for code in picked_codes):
                QtWidgets.QMessageBox.warning(self, "Comparativo", "Error asignando condiciones.")
                return

            if len(set(picked_codes)) != len(picked_codes):
                QtWidgets.QMessageBox.warning(self, "Comparativo", "Cada sesión debe tener una condición distinta.")
                return

            mapping = {code: sessions[idx] for idx, code in enumerate(picked_codes)}

        # ---- cargar snapshots + trails ----
        for code in CONDITION_CODES:
            self.snapshots[code] = None
        self.cmp_trails = {}

        for cond, s in mapping.items():
            snap, trails = self._load_trails_and_snapshot(s["csv_path"])
            if snap is None or trails is None:
                QtWidgets.QMessageBox.warning(self, "Comparativo", f"CSV vacío o inválido:\n{s['csv_path']}")
                return

            snap["session_name"] = s["label"]
            self.snapshots[cond] = snap
            self.cmp_trails[cond] = trails

        # mostrar todo
        for code, chk in self.cmp_checks.items():
            chk.setChecked(code in mapping)

        self.render_comparative()
        self.tabs.setCurrentWidget(self.tab_cmp)

    def replay_speed_changed(self, txt: str):
        # "0.5x", "1x", "2x", "4x"
        try:
            self.replay_speed = float(txt.replace("x", ""))
        except:
            self.replay_speed = 1.0

    def replay_toggle_play(self):
        if not self.replay_data:
            return
        if self.replay_playing:
            self.replay_playing = False
            self.replay_timer.stop()
            self.btn_rep_play.setText("Play")
        else:
            self.replay_playing = True
            self.replay_timer.start()
            self.btn_rep_play.setText("Pause")

    def replay_stop(self):
        if not self.replay_data:
            return
        self.replay_playing = False
        self.replay_timer.stop()
        self.replay_idx = 0
        self.btn_rep_play.setText("Play")
        self.replay_draw_index(0)
        self.rep_slider.blockSignals(True)
        self.rep_slider.setValue(0)
        self.rep_slider.blockSignals(False)

    def replay_slider_changed(self, idx: int):
        if not self.replay_data:
            return
        self.replay_idx = int(idx)
        self.replay_draw_index(self.replay_idx)

    def replay_tick(self):
        if not self.replay_data or not self.replay_playing:
            return

        # avanzamos según speed (saltando índices)
        step = max(1, int(round(self.replay_speed)))
        self.replay_idx += step
        if self.replay_idx >= len(self.replay_data["t"]):
            # fin: pausamos en el último
            self.replay_idx = len(self.replay_data["t"]) - 1
            self.replay_playing = False
            self.replay_timer.stop()
            self.btn_rep_play.setText("Play")

        self.rep_slider.blockSignals(True)
        self.rep_slider.setValue(self.replay_idx)
        self.rep_slider.blockSignals(False)

        self.replay_draw_index(self.replay_idx)

    def replay_redraw_trail(self):
        # Redibuja trayectoria hasta el índice actual
        if not self.replay_data:
            return
        self.replay_draw_index(self.replay_idx)

    def replay_draw_index(self, i: int):
        d = self.replay_data
        if not d:
            return

        t = d["t"][i]
        xg, yg = d["xg"][i], d["yg"][i]
        xl, yl = d["xl"][i], d["yl"][i]
        xr, yr = d["xr"][i], d["yr"][i]
        tor = d["tor"][i]

        # puntos (B)
        self.rep_dot_g.setData([xg], [yg])
        self.rep_dot_l.setData([xl], [yl])
        self.rep_dot_r.setData([xr], [yr])

        # torsión
        xs, ys = self.segment_for_angle(tor, length=20.0)
        self.rep_tor_line.setData(xs, ys)

        if self.chk_rep_trail.isChecked():
            self.rep_traj_curve.setData(d["xg"][:i + 1], d["yg"][:i + 1])
            self.rep_traj_curve_l.setData(d["xl"][:i + 1], d["yl"][:i + 1])
            self.rep_traj_curve_r.setData(d["xr"][:i + 1], d["yr"][:i + 1])
        else:
            self.rep_traj_curve.setData([], [])
            self.rep_traj_curve_l.setData([], [])
            self.rep_traj_curve_r.setData([], [])

        self.rep_time_lbl.setText(f"t = {t:.2f} s")
    # ---------- Main loop ----------
    def update_loop(self):
        if not self.serial_ok:
            return

        frame = self.read_last_valid_frame()
        if frame is None:
            return

        if self.paused:
            return

        (p0,p1,p2,p3,p4,p5,
         xg,yg,xl,yl,xr,yr,
         PL,PR) = frame

        xg = self.ema_xg.update(xg); yg = self.ema_yg.update(yg)
        xl = self.ema_xl.update(xl); yl = self.ema_yl.update(yl)
        xr = self.ema_xr.update(xr); yr = self.ema_yr.update(yr)

        self.trail_g.append((xg, yg))
        self.trail_l.append((xl, yl))
        self.trail_r.append((xr, yr))

        if self.trail_g:
            xs, ys = zip(*self.trail_g)
            self.curve_g.setData(xs, ys)
        if self.trail_l:
            xs, ys = zip(*self.trail_l)
            self.curve_l.setData(xs, ys)
        if self.trail_r:
            xs, ys = zip(*self.trail_r)
            self.curve_r.setData(xs, ys)

        self.dot_g.setData([xg],[yg])
        self.dot_l.setData([xl],[yl])
        self.dot_r.setData([xr],[yr])

        total = PL + PR
        if total > 0:
            left_pct = 100.0 * PL / total
            right_pct = 100.0 * PR / total
            overload = abs(PL - PR) / total
            self.balance.setValue(int(round(right_pct)))
            self.lbl_weights.setText(
                f"PL: {PL:.0f} | PR: {PR:.0f} | Izq: {left_pct:5.1f}% Der: {right_pct:5.1f}% | Overload: {overload:0.2f}"
            )
        else:
            overload = 0.0
            self.balance.setValue(50)
            self.lbl_weights.setText("PL: --- | PR: --- | Izq: ---% Der: --- % | Overload: ---")

        t = time.time()
        self.metric_win.add(t, xg, yg)
        m = self.metric_win.compute()

        torsion_deg = self.torsion_deg_from_feet(xl,yl,xr,yr)

        self.lbl_metrics.setText(
            f"Sway: {m.sway_path:7.2f} cm | Vel: {m.mean_speed:6.2f} cm/s | RMSx: {m.rms_x:5.2f} | RMSy: {m.rms_y:5.2f} | Torsión: {torsion_deg:+.2f}°"
        )

        kapL, kapR = self.compute_kapandji_loads(p0,p1,p2,p3,p4,p5)
        self.update_kapandji_overlay(kapL, kapR, PT=PL+PR)

        xs, ys = self.segment_for_angle(torsion_deg, length=40.0)
        self.line_t_live.setData(xs, ys)

        for cond, line in self.line_t_by_cond.items():
            snap = self.snapshots.get(cond)
            if snap:
                xs2, ys2 = self.segment_for_angle(snap["torsion_deg"], length=40.0)
                line.setData(xs2, ys2)
            else:
                line.setData([], [])

        rec = {
            "t": t,
            "xg": xg, "yg": yg, "xl": xl, "yl": yl, "xr": xr, "yr": yr,
            "PL": PL, "PR": PR,
            "overload": overload,
            "torsion_deg": torsion_deg,
            "L_med": kapL[0], "L_lat": kapL[1], "L_heel": kapL[2],
            "R_med": kapR[0], "R_lat": kapR[1], "R_heel": kapR[2],
        }
        self.last_processed = rec
        self.recent.append(rec)

        if self.recording and self.csv_writer:
            if (not PAUSE_STOPS_RECORDING_WRITE) or (not self.paused):
                self.csv_writer.writerow([
                    t,
                    p0,p1,p2,p3,p4,p5,
                    xg,yg,xl,yl,xr,yr,
                    PL,PR,
                    overload, torsion_deg,
                    m.sway_path, m.mean_speed, m.rms_x, m.rms_y,
                    self.session_condition
                ])

    def delete_selected_session(self):
        if not self.current_patient:
            QtWidgets.QMessageBox.warning(self, "Borrar grabación", "Seleccioná un paciente primero.")
            return

        item = self.list_sessions.currentItem()
        if not item:
            QtWidgets.QMessageBox.information(self, "Borrar grabación", "Seleccioná una grabación primero.")
            return

        _, pname, _ = self.current_patient

        folder = item.data(QtCore.Qt.UserRole)
        if not folder:
            QtWidgets.QMessageBox.warning(self, "Borrar grabación", "Sesión inválida (no tiene carpeta asociada).")
            return

        session_dir = os.path.join(self.patient_folder(pname), folder)

        if not os.path.isdir(session_dir):
            QtWidgets.QMessageBox.warning(self, "Borrar grabación", f"No existe la carpeta:\n{session_dir}")
            return

        resp = QtWidgets.QMessageBox.question(
            self,
            "Confirmar borrado",
            f"¿Seguro que querés borrar esta grabación?\n\n{item.text()}\n\nSe eliminará la carpeta completa.",
            QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No,
            QtWidgets.QMessageBox.No
        )
        if resp != QtWidgets.QMessageBox.Yes:
            return

        try:
            import shutil
            shutil.rmtree(session_dir)
        except Exception as e:
            QtWidgets.QMessageBox.critical(self, "Borrar grabación", f"No pude borrar:\n{e}")
            return

        # limpiar selección comparativo/replay si apuntaban a esto
        for k in CONDITION_CODES:
            snap = self.snapshots.get(k)
            if snap and snap.get("session_name") == item.text():
                self.snapshots[k] = None
        if hasattr(self, "cmp_trails"):
            for k in CONDITION_CODES:
                if self.cmp_trails.get(k):
                    # no sabemos si era esa sesión; lo más seguro es vaciar y que vuelvan a comparar
                    self.cmp_trails.pop(k, None)

        self.refresh_sessions()
        self.statusBar().showMessage("Grabación borrada.")

    def closeEvent(self, event):
        try:
            self.stop_recording()
        except:
            pass
        try:
            if self.ser and self.ser.is_open:
                self.ser.close()
        except:
            pass
        try:
            self.con.close()
        except:
            pass
        event.accept()


if __name__ == "__main__":
    ensure_dirs()
    app = QtWidgets.QApplication(sys.argv)
    win = MainWindow()
    win.resize(1500, 850)
    win.show()
    sys.exit(app.exec())
