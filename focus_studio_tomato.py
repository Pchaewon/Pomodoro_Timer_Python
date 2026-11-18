# -*- coding: utf-8 -*-
"""Tomato Focus — Tkinter Pomodoro, To-do, meeting reminders and week/month/year focus dashboard.

Standalone: Python 3.9+ and the standard library only.
Light/dark theme: use the moon/sun toggle or Settings > 화면 테마.
    python focus_studio_tomato.py
    python focus_studio_tomato.py --demo

Build on Windows:
    pyinstaller --onefile --windowed --name TomatoFocus focus_studio_tomato.py

Your previous Focus Studio data remains compatible:
    ~/.focus_studio/state.json
New fields are added without deleting old tasks or completed sessions.
"""
from __future__ import annotations

import argparse
import calendar
import ctypes
from datetime import date, datetime, timedelta
import json
import logging
from logging.handlers import RotatingFileHandler
import math
from pathlib import Path
import random
import sys
import time
import tkinter as tk
from tkinter import font as tkfont, messagebox, simpledialog
from statistics import median
from difflib import SequenceMatcher
import uuid

APP_NAME = "Tomato Focus"
DATA_PATH = Path.home() / ".focus_studio" / "state.json"
LOG_PATH = DATA_PATH.with_name("tomato_focus.log")
LOGGER = logging.getLogger("tomato_focus")


def configure_logging():
    """Bounded diagnostic log, including windowed EXE callback errors."""
    if LOGGER.handlers:
        return
    LOGGER.setLevel(logging.INFO)
    LOGGER.propagate = False
    try:
        LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
        handler = RotatingFileHandler(LOG_PATH, maxBytes=256 * 1024,
                                      backupCount=1, encoding="utf-8")
        handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
        LOGGER.addHandler(handler)
    except OSError:
        LOGGER.addHandler(logging.NullHandler())


# Theme colors are semantic: "white" means card/background surface, not literal white.
# Widgets read from the same mutable dict and get rebuilt after a theme change.
THEMES = {
    "light": {
        "bg": "#FFF8F3", "white": "#FFFFFF", "surface": "#FFF1E8",
        "surface2": "#FFE8DB", "line": "#EEDFD5", "text": "#332923",
        "muted": "#8D7D73", "hint": "#B2A29A", "red": "#E64A32",
        "red_dark": "#B93524", "red_pale": "#FBE2D9", "orange": "#FA9C63",
        "orange_pale": "#FFE3CF", "green": "#4B854D",
        "green_light": "#78A663", "gray_btn": "#F7F2EF", "shadow": "#F1DBCD",
        "on_accent": "#FFFFFF",
        "heatmap": ("#FBF0E9", "#FFD4B8", "#FFAC79", "#F3754D", "#C84326"),
    },
    "dark": {
        "bg": "#15191D", "white": "#22282D", "surface": "#2C3238",
        "surface2": "#353B42", "line": "#3E464D", "text": "#F5EEE9",
        "muted": "#B9AAA2", "hint": "#938985", "red": "#FF7058",
        "red_dark": "#E65742", "red_pale": "#4A302D", "orange": "#F3AA76",
        "orange_pale": "#50392C", "green": "#89C58C",
        "green_light": "#A6D1A0", "gray_btn": "#30373D", "shadow": "#111518",
        "on_accent": "#201C1A",
        "heatmap": ("#303137", "#583F3A", "#92503C", "#CE6245", "#FF805A"),
    },
}
P = dict(THEMES["light"])


def apply_palette(theme):
    """Switch all canvas/frame/pill semantic colors before rebuilding Tk widgets."""
    if theme not in THEMES:
        theme = "light"
    P.clear()
    P.update(THEMES[theme])

DEFAULT_SETTINGS = {
    "focus": 25,
    "short": 10,
    "long": 30,
    "long_every": 4,
    "daily_goal": 120,
    "always_on_top": False,         # Full dashboard only
    "mini_always_on_top": True,     # Floating widget: ON by default
    "auto_break": False,
    "prevent_sleep": True,     # Windows only: prevent automatic system sleep, not display-off
    "theme": "light",          # "light" / "dark", persisted across launches
}
MODE_TITLE = {"focus": "몰입 시간", "short": "짧은 휴식", "long": "긴 휴식"}
MODE_TAG = {"focus": "FOCUS", "short": "SHORT BREAK", "long": "LONG BREAK"}
DAY_KO = ["월", "화", "수", "목", "금", "토", "일"]


def font_family(root):
    root = root._root()
    if getattr(root, "_tomato_font_family", None):
        return root._tomato_font_family
    families = set(tkfont.families(root))
    for f in ("Pretendard", "맑은 고딕", "Malgun Gothic", "Apple SD Gothic Neo",
              "Noto Sans CJK KR", "Segoe UI", "DejaVu Sans"):
        if f in families:
            root._tomato_font_family = f
            return f
    root._tomato_font_family = "TkDefaultFont"
    return root._tomato_font_family


def rounded_rect(cv, x1, y1, x2, y2, r=16, *, fill, outline="", width=1, tags=()):
    """Draw a smooth rounded polygon, no additional graphics dependencies."""
    r = max(0, min(r, (x2-x1)/2, (y2-y1)/2))
    p = [x1+r,y1, x2-r,y1, x2,y1,x2,y1+r,
         x2,y2-r, x2,y2,x2-r,y2, x1+r,y2,
         x1,y2,x1,y2-r, x1,y1+r, x1,y1]
    return cv.create_polygon(p, fill=fill, outline=outline, width=width, smooth=True, splinesteps=20, tags=tags)


def solid_color(level):
    colors = P["heatmap"]
    if level <= 0:
        return colors[0]
    if level < 35:
        return colors[1]
    if level < 75:
        return colors[2]
    if level < 120:
        return colors[3]
    return colors[4]


class Pill(tk.Canvas):
    def __init__(self, parent, text, command, *, width=120, height=39,
                 fill="white", fg="text", border=None, hover=None,
                 radius=15, fontsize=10, bold=True):
        bg = parent.cget("bg")
        super().__init__(parent, bg=bg, width=width, height=height,
                         bd=0, highlightthickness=0, cursor="hand2", takefocus=1)
        self.text, self.command = text, command
        self.fill = P.get(fill, fill)
        self.fg = P.get(fg, fg)
        self.border = P.get(border, border) if border else None
        self.hover = P.get(hover, hover) if hover else self.fill
        self.radius = radius
        self.fontsize = fontsize
        self.bold = bold
        self.hot = False
        self.fname = font_family(self.winfo_toplevel())
        self.bind("<Configure>", lambda e: self.draw())
        self.bind("<Enter>", self.enter)
        self.bind("<Leave>", self.leave)
        self.bind("<Button-1>", lambda e: self.command())
        self.bind("<Return>", lambda e: self.command())
        self.bind("<space>", lambda e: self.command())
        self.draw()

    def enter(self, _evt):
        self.hot = True
        self.draw()

    def leave(self, _evt):
        self.hot = False
        self.draw()

    def set(self, *, text=None, fill=None, fg=None):
        old = (self.text, self.fill, self.fg, self.hover)
        if text is not None:
            self.text = text
        if fill is not None:
            new_fill = P.get(fill, fill)
            if self.hover == self.fill:
                self.hover = new_fill
            self.fill = new_fill
        if fg is not None:
            self.fg = P.get(fg, fg)
        if old != (self.text, self.fill, self.fg, self.hover):
            self.draw()

    def draw(self):
        self.delete("all")
        w = int(self.winfo_width() or self.cget("width"))
        h = int(self.winfo_height() or self.cget("height"))
        rounded_rect(self, 1.5, 1.5, w-1.5, h-1.5, self.radius,
                     fill=self.hover if self.hot else self.fill,
                     outline=self.border or "", width=1)
        self.create_text(w/2, h/2, text=self.text,
                         fill=self.fg, font=(self.fname, self.fontsize, "bold" if self.bold else "normal"))


class WhiteCard(tk.Frame):
    """White content panel; an outer thin border keeps it crisp in Tk 8.6."""
    def __init__(self, parent, *, padding=18, bg="white", **kw):
        super().__init__(parent, bg=P[bg], highlightthickness=1,
                         highlightbackground=P["line"], bd=0, **kw)
        self.body = tk.Frame(self, bg=P[bg], padx=padding, pady=padding)
        self.body.pack(fill="both", expand=True)


def draw_tomato(cv: tk.Canvas, cx, cy, scale=1.0, *, outline=False, speckles=True):
    """Hand-made, grain-accented tomato mark drawn entirely with Tk Canvas."""
    s = scale
    def pt(dx, dy): return cx+dx*s, cy+dy*s
    if outline:
        cv.create_oval(*pt(-17,-11), *pt(17,17), fill=P["white"], outline=P["line"], width=max(1,1.6*s))
    else:
        cv.create_oval(*pt(-17,-11), *pt(17,17), fill=P["red"], outline=P["red_dark"], width=max(1, 0.8*s))
        if speckles and s > .8:
            rng = random.Random(212)
            for i in range(19):
                x, y = rng.uniform(-13, 13), rng.uniform(-8, 12)
                if (x/16)**2 + ((y-2)/15)**2 < .85:
                    xx, yy = pt(x,y)
                    rr = max(.6, .55*s)
                    cv.create_oval(xx-rr, yy-rr, xx+rr, yy+rr,
                                   fill="#EF7458", outline="")
    leaf = [(-2,-10),(-14,-10),(-8,-16),(-20,-18),(-7,-18),(-9,-27),
            (0,-19),(9,-25),(6,-17),(18,-20),(10,-13),(4,-11)]
    coords = []
    for a,b in leaf:
        coords.extend(pt(a,b))
    cv.create_polygon(coords, fill=P["green"], outline="#346B37", width=max(1,s*.7), smooth=True)
    cv.create_line(*pt(-1,-20),*pt(2,-29), fill="#346B37", width=max(1,2*s), capstyle="round")


def draw_tomato_scene(cv: tk.Canvas, mode="focus"):
    """Vector tomato mascot; works when bundled with PyInstaller (no asset files)."""
    cv.delete("scene")
    w = cv.winfo_width() or int(cv.cget("width"))
    h = cv.winfo_height() or int(cv.cget("height"))
    scale = min(w/330, h/174)
    ox = (w-330*scale)/2
    oy = (h-174*scale)/2
    def pos(x,y): return ox+x*scale, oy+y*scale
    def oval(a,b,c,d, **kw): return cv.create_oval(*pos(a,b),*pos(c,d), tags="scene", **kw)
    def rect(a,b,c,d, **kw): return cv.create_rectangle(*pos(a,b),*pos(c,d), tags="scene", **kw)
    def line(*pts, **kw):
        coords=[]
        for x,y in pts: coords.extend(pos(x,y))
        return cv.create_line(*coords, tags="scene", **kw)
    def poly(pts, **kw):
        coords=[]
        for x,y in pts: coords.extend(pos(x,y))
        return cv.create_polygon(*coords, tags="scene", **kw)
    # Pale floating graphic, like the mobile design reference.
    oval(72,12,258,169,fill=P["surface"],outline="")
    if mode == "focus":
        # Table & tiny laptop, sitting work mascot.
        rect(89,125,238,134,fill="#BC855F",outline="#9C644A",width=1)
        line((102,134),(99,163),fill="#996345",width=max(2,3*scale))
        line((226,134),(231,163),fill="#996345",width=max(2,3*scale))
        oval(126,99,198,151,fill="#E95740",outline="#B83F2C",width=max(1,scale))
        oval(121,43,215,122,fill=P["red"],outline=P["red_dark"],width=max(1,1.5*scale))
        # little leaves
        poly([(165,49),(149,37),(164,40),(166,29),(172,41),(188,35),(180,48),(192,48),
              (176,55)],fill=P["green"],outline="#33693C",width=max(1,scale),smooth=True)
        # rim & glasses
        rect(140,75,158,89,fill="#FFB389",outline="#49362D",width=max(1,1.7*scale))
        rect(173,75,191,89,fill="#FFB389",outline="#49362D",width=max(1,1.7*scale))
        line((158,80),(173,80),fill="#49362D",width=max(1,1.8*scale))
        oval(148,82,151,85,fill="#43352C",outline="")
        oval(181,82,184,85,fill="#43352C",outline="")
        line((159,97),(168,101),(177,97),fill="#8D3328",width=max(1,1.5*scale),smooth=True)
        line((146,116),(133,125),fill="#D74732",width=max(2,4*scale))
        line((184,116),(197,125),fill="#D74732",width=max(2,4*scale))
        poly([(95,101),(150,101),(160,128),(106,128)],fill="#9FB1B7",outline="#76888D",width=max(1,scale))
        rect(105,128,175,132,fill="#74878B",outline="")
        oval(202,112,220,130,fill="#FFF1DF",outline="#C68E6D",width=max(1,scale))
        line((220,116),(228,115),(228,125),(220,125),fill="#C68E6D",width=max(1,scale))
    else:
        # Tomato taking a break in an upholstered beanbag.
        oval(104,81,229,160,fill="#8CA5CE",outline="#667FA9",width=max(1,scale))
        oval(121,42,212,122,fill=P["red"],outline=P["red_dark"],width=max(1,1.5*scale))
        poly([(162,48),(149,36),(164,40),(169,28),(174,42),(193,37),(180,50)],
             fill=P["green"],outline="#33693C",smooth=True)
        rect(139,79,157,91,fill="#FFC39C",outline="#49362D",width=max(1,1.5*scale))
        rect(174,79,192,91,fill="#FFC39C",outline="#49362D",width=max(1,1.5*scale))
        line((157,82),(174,82),fill="#49362D",width=max(1,1.5*scale))
        line((144,86),(152,86),fill="#49362D",width=max(1,1.5*scale))
        line((179,86),(187,86),fill="#49362D",width=max(1,1.5*scale))
        line((164,105),(173,108),(179,105),fill="#842E21",width=max(1,1.4*scale),smooth=True)
        oval(155,117,183,138,fill="#FFF5E9",outline="#A97657",width=max(1,scale))
        line((183,121),(190,121),(190,132),(183,132),fill="#A97657",width=max(1,scale))
        oval(146,143,172,152,fill="#F2724B",outline="")
        oval(188,139,213,149,fill="#F2724B",outline="")


class TomatoFocus:
    def __init__(self, root: tk.Tk, demo=False, screenshot=None):
        self.root = root
        self.demo = demo
        self.screenshot = screenshot
        self.font_name = font_family(root)
        self.done_font = tkfont.Font(root=root, family=self.font_name, size=10, overstrike=True)
        self._closing = False
        self._tick_after = self._meeting_after = self._topmost_after = None
        self._sleep_active = False
        self._task_render_key = None
        self._meeting_summary_key = None
        self._stats_cache = None
        self._session_revision = 0
        self._last_day = date.today()
        self.root.report_callback_exception = self.report_callback_exception
        self.state = self.load()
        if demo:
            self.add_demo_content()
        self.settings = self.state["settings"]
        self._daily_stats = {}
        self._task_seconds = {}
        self.session_task = None
        self.segment_started = None
        self.segment_budget = 0
        self.session_seconds = 0
        for session in self.state["sessions"]:
            self._index_session(session)
        apply_palette(self.settings.get("theme", "light"))
        self.mode = "focus"
        self.page = "focus"
        self.period = "week"
        self.anchor_day = date.today()
        self.compact = False
        self.running = False
        self.remaining = self.settings["focus"] * 60
        self.deadline = None
        self.pause_since = None
        self.pause_total = 0
        self.pause_count = 0
        self.focus_started_at = None
        self.session_started = False
        self.status = "오늘의 작은 몰입을 시작해 보세요."
        self.active_task = self.state.get("active_task")
        self.focus_cycle = sum(1 for s in self.state["sessions"] if s.get("date") == date.today().isoformat() and s.get("mode", "focus") == "focus" and not s.get("partial")) % self.settings["long_every"]
        self.filter_name = "all"
        self.summary_value = {}
        self.advice_label = None
        self._advice_widget = None
        self.timer_label = None
        self.primary_button = None
        self.mode_buttons = {}
        self.status_label = None
        self.cycle_canvas = None
        self.scene = None
        self.task_area = None
        self.entry = None
        self.task_scroll = None
        self.nav_buttons = {}
        self.period_buttons = {}
        self.chart_canvas = None
        self.heat_canvas = None
        self.stats_summary = {}
        self.period_caption = None
        self.stats_info = None
        self.mini_pin = None
        self.mini_task_label = None
        self.drag_start = None
        self.meeting_filter = "upcoming"
        self.meeting_popups = []
        self.break_popup = None
        self.meeting_list = self.meeting_next = self.meeting_next_detail = None
        self.mini_meeting_label = None
        self.meeting_view_key = None
        self.full_geometry = "1100x930"
        self.root.title(APP_NAME)
        self.root.configure(bg=P["bg"])
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.bind("<space>", self.spacebar)
        self.root.bind("<Control-n>", self.quick_add)
        self.root.bind("<Control-m>", lambda e: self.toggle_mini())
        self.root.bind("<Control-e>", self.open_meetings)
        self.root.bind("<Control-q>", self.close)
        self.root.bind("<Escape>", lambda e: self.toggle_mini() if self.compact else None)
        self.root.geometry(self.full_geometry)
        self.root.minsize(900, 720)
        self.root.resizable(True, True)
        self.build()
        self._schedule_tick()
        self._meeting_after = self.root.after(250, self.meeting_tick)
        self.apply_topmost()
        self.apply_sleep_policy()
        LOGGER.info("Started (demo=%s, theme=%s)", self.demo, self.settings["theme"])
        if screenshot:
            # Only used for optional development previews. Pillow is not needed to run the app.
            self.root.after(850, lambda: self.capture(screenshot))

    @staticmethod
    def fresh_state():
        return {"tasks": [], "sessions": [], "settings": dict(DEFAULT_SETTINGS),
                "active_task": None, "window": {}, "meetings": [], "breaks": [], "task_completion_log": []}

    def load(self):
        state = self.fresh_state()
        try:
            existing = json.loads(DATA_PATH.read_text(encoding="utf-8"))
            if not isinstance(existing, dict):
                return state
            state["tasks"] = [x for x in existing.get("tasks", []) if isinstance(x, dict)] if isinstance(existing.get("tasks", []), list) else []
            state["sessions"] = [x for x in existing.get("sessions", []) if isinstance(x, dict)] if isinstance(existing.get("sessions", []), list) else []
            for key in ("breaks", "task_completion_log"):
                if isinstance(existing.get(key), list):
                    state[key] = [x for x in existing[key] if isinstance(x, dict)]
            meetings = existing.get("meetings", [])
            if isinstance(meetings, list):
                for item in meetings:
                    if not isinstance(item, dict) or not self.meeting_time(item): continue
                    if not isinstance(item.get("title"), str) or not item["title"].strip(): continue
                    if item.get("remind_minutes") not in (10, 15): continue
                    state["meetings"].append({"id": str(item.get("id") or uuid.uuid4().hex),
                                              "title": item["title"], "start_at": self.meeting_time(item).isoformat(timespec="minutes"),
                                              "remind_minutes": int(item["remind_minutes"]), "notified": item.get("notified") is True})
            state["active_task"] = existing.get("active_task")
            state["window"] = existing.get("window", {}) if isinstance(existing.get("window", {}), dict) else {}
            old = existing.get("settings", {})
            if isinstance(old, dict):
                for key, default in DEFAULT_SETTINGS.items():
                    value = old.get(key, default)
                    if isinstance(default, bool) and isinstance(value, bool):
                        state["settings"][key] = value
                    elif type(default) is int and type(value) is int and 1 <= value <= 999:
                        state["settings"][key] = value
                    elif key == "theme" and value in THEMES:
                        state["settings"][key] = value
        except (OSError, ValueError, TypeError):
            pass
        state["settings"]["long_every"] = max(1,min(20,state["settings"]["long_every"]))
        return state

    def add_demo_content(self):
        today = date.today()
        tasks = ["주간 보고서 정리", "AI 추천 로직 확인", "실험 결과 비교", "회의 노트 정리", "내일 우선순위 지정"]
        self.state["tasks"] = [
            {"id": f"demo-{i}", "title": title, "done": i == 0, "priority": i==1,
             "created_at": today.isoformat(), "completed_on": today.isoformat() if i==0 else None}
            for i,title in enumerate(tasks)
        ]
        self.state["active_task"] = "demo-1"
        future = (datetime.now()+timedelta(hours=1)).replace(second=0, microsecond=0)
        self.state["meetings"] = [
            {"id": "demo-meeting-1", "title": "프로젝트 진행 현황 리뷰", "start_at": future.isoformat(timespec="minutes"), "remind_minutes": 10, "notified": False},
            {"id": "demo-meeting-2", "title": "팀 주간 회의", "start_at": (future+timedelta(days=1)).isoformat(timespec="minutes"), "remind_minutes": 15, "notified": False},
        ]
        rng = random.Random(30)
        self.state["sessions"] = []
        for i in range(185):
            dt = today - timedelta(days=i)
            if rng.random() < .26: continue
            for _ in range(rng.choice([1,2,2,3,3,4,5])):
                self.state["sessions"].append({"date":dt.isoformat(), "minutes": 25,
                        "task_id": "demo-1", "task_title": "AI 추천 로직 확인",
                        "pause_count":rng.choice([0,0,0,1,2])})

    def save(self):
        if self.demo: return
        self.state["active_task"] = self.active_task
        try:
            DATA_PATH.parent.mkdir(parents=True, exist_ok=True)
            temp = DATA_PATH.with_suffix(".tmp")
            with temp.open("w", encoding="utf-8") as stream:
                json.dump(self.state, stream, ensure_ascii=False, indent=2)
            temp.replace(DATA_PATH)
        except OSError as e:
            self.status = f"저장하지 못했습니다: {e}"
            LOGGER.exception("State save failed")

    def label(self, parent, text, *, size=11, color="text", weight="normal", bg=None, **kw):
        return tk.Label(parent, text=text, bg=bg or parent.cget("bg"), fg=P.get(color, color),
                        font=(self.font_name,size,weight), **kw)

    def btn(self, parent, text, command, *, width=115, height=38, fill="white", fg="text",
            border=None, hover=None, radius=14, size=10):
        return Pill(parent,text,command,width=width,height=height,fill=fill,fg=fg,
                    border=border,hover=hover,radius=radius,fontsize=size)

    def clear_widgets(self):
        for child in self.root.winfo_children():
            if child not in self.meeting_popups and child is not self.break_popup: child.destroy()
        self.summary_value = {}
        self.advice_label = None
        self._advice_widget = None
        self.timer_label = self.primary_button = self.status_label = self.cycle_canvas = None
        self.scene = self.task_area = self.entry = self.task_scroll = None
        self.nav_buttons, self.mode_buttons, self.period_buttons = {}, {}, {}
        self.chart_canvas = self.heat_canvas = self.period_caption = self.stats_info = None
        self.stats_summary = {}
        self.mini_pin = self.mini_task_label = None
        self.meeting_list = self.meeting_next = self.meeting_next_detail = None
        self.mini_meeting_label = None
        self.meeting_view_key = None
        self._task_render_key = self._meeting_summary_key = None
        self.current_task = self.task_count = self.scroll_window = None
        self.task_filter_buttons = self.meeting_filter_buttons = {}
        self.meeting_canvas = self.meeting_wheel = None

    def build(self):
        self.clear_widgets()
        self.root.configure(bg=P["bg"])
        if self.compact:
            self.build_mini()
        else:
            self.build_full()
        self.refresh()

    def build_full(self):
        self.root.overrideredirect(False)
        self.root.resizable(True,True)
        self.root.minsize(900,720)
        shell = tk.Frame(self.root,bg=P["bg"],padx=28,pady=19)
        shell.pack(fill="both",expand=True)
        hdr = tk.Frame(shell,bg=P["bg"])
        hdr.pack(fill="x",pady=(0,16))
        logo = tk.Canvas(hdr,bg=P["bg"],width=43,height=43,highlightthickness=0)
        logo.pack(side="left")
        draw_tomato(logo,21,27,0.95)
        titlebox=tk.Frame(hdr,bg=P["bg"])
        titlebox.pack(side="left",padx=(8,0))
        self.label(titlebox,"TOMATO",size=17,color="red",weight="bold").pack(anchor="w")
        self.label(titlebox,"FOCUS  ·  나만의 몰입 공간",size=9,color="muted").pack(anchor="w")
        right=tk.Frame(hdr,bg=P["bg"])
        right.pack(side="right")
        self.btn(right,"⚙ 설정",self.settings_dialog,width=74,height=37,fill="white",border="line").pack(side="right",padx=(8,0))
        self.btn(right,"☾ 다크" if self.settings["theme"] == "light" else "☀ 라이트",
                 self.toggle_theme,width=76,height=37,fill="surface",fg="text",border="line").pack(side="right",padx=(8,0))
        self.btn(right,"▣ 미니 위젯",self.toggle_mini,width=106,height=37,fill="red",fg="on_accent",hover="red_dark").pack(side="right",padx=(8,0))
        for pg,name in (("focus","집중 · 할 일"),("stats","몰입 통계"),("meetings","회의")):
            b = self.btn(right,name,lambda p=pg:self.switch_page(p),width=99 if pg!="meetings" else 70,height=37,
                         fill="red_pale" if pg==self.page else "white",
                         fg="red" if pg==self.page else "muted",
                         border=None if pg==self.page else "line")
            b.pack(side="left",padx=(0,7))
            self.nav_buttons[pg]=b
        if self.page=="focus":
            self.build_dashboard(shell)
        elif self.page=="stats":
            self.build_statistics(shell)
        else:
            self.build_meetings(shell)
        foot=tk.Frame(shell,bg=P["bg"])
        foot.pack(fill="x",pady=(10,0))
        self.status_label=self.label(foot,"",size=9,color="muted")
        self.status_label.pack(side="left")
        self.label(foot,"SPACE 시작/멈춤  ·  CTRL+N 할 일  ·  CTRL+M 미니  ·  CTRL+E 회의",
                   size=9,color="hint").pack(side="right")

    def build_dashboard(self, shell):
        top=tk.Frame(shell,bg=P["bg"])
        top.pack(fill="x",pady=(0,15))
        dt=datetime.now()
        self.label(top,"오늘도, 토마토 한 알만큼 집중해요.",size=19,weight="bold").pack(anchor="w")
        self.label(top,f"{dt:%Y.%m.%d}  ·  작고 꾸준한 몰입의 기록",size=10,color="muted").pack(anchor="w",pady=(3,0))
        advice=WhiteCard(shell,padding=9)
        advice.pack(fill="x",pady=(0,9))
        self.label(advice.body,"🍅 오늘의 한마디 · 어제의 기록",size=10,color="red",weight="bold").pack(anchor="w")
        self.advice_label=self.label(advice.body,self.daily_advice(),size=10,justify="left",wraplength=790)
        self.advice_label.pack(anchor="w",pady=(3,0))
        summaries=tk.Frame(shell,bg=P["bg"],height=94)
        summaries.pack(fill="x",pady=(0,13))
        summaries.pack_propagate(False)
        for idx,(key,title,unit) in enumerate((("minutes","오늘 집중","분"),("sessions","완료한 세션","회"),("tasks","완료한 할 일","개"),("goal","오늘 목표 달성","%"))):
            card=WhiteCard(summaries,padding=10)
            card.pack(side="left",fill="both",expand=True,padx=(0,9) if idx<3 else 0)
            self.label(card.body,title,size=10,color="muted").pack(anchor="w")
            row=tk.Frame(card.body,bg=P["white"])
            row.pack(anchor="w",pady=(4,0))
            txt=self.label(row,"—",size=21,color="red" if idx==0 else "text",weight="bold")
            txt.pack(side="left")
            self.label(row,unit,size=10,color="muted").pack(side="left",padx=(4,0),pady=(5,0))
            self.summary_value[key]=txt
        main=tk.Frame(shell,bg=P["bg"])
        main.pack(fill="both",expand=True)
        main.grid_columnconfigure(0,weight=10,uniform="block")
        main.grid_columnconfigure(1,weight=11,uniform="block")
        main.grid_rowconfigure(0,weight=1)
        left=WhiteCard(main,padding=18)
        left.grid(row=0,column=0,sticky="nsew",padx=(0,13))
        right=WhiteCard(main,padding=19)
        right.grid(row=0,column=1,sticky="nsew")
        self.build_timer(left.body,mini=False)
        self.build_tasks(right.body)

    def build_mini(self):
        self.root.overrideredirect(True)
        self.root.resizable(False,False)
        self.root.minsize(1,1)
        location=self.state.get("window",{})
        x=location.get("mini_x")
        y=location.get("mini_y")
        if not isinstance(x,int) or not isinstance(y,int):
            self.root.update_idletasks()
            x=max(0,self.root.winfo_screenwidth()-345)
            y=64
        x=max(0,min(x,max(0,self.root.winfo_screenwidth()-320)))
        y=max(0,min(y,max(0,self.root.winfo_screenheight()-463)))
        self.root.geometry(f"320x458+{x}+{y}")
        outer=tk.Frame(self.root,bg=P["shadow"],padx=1,pady=1)
        outer.pack(fill="both",expand=True)
        panel=tk.Frame(outer,bg=P["white"],padx=16,pady=10)
        panel.pack(fill="both",expand=True)
        header=tk.Frame(panel,bg=P["white"],cursor="fleur",height=41)
        header.pack(fill="x",pady=(0,4))
        header.pack_propagate(False)
        mark=tk.Canvas(header,width=29,height=32,bg=P["white"],highlightthickness=0,cursor="fleur")
        mark.pack(side="left")
        draw_tomato(mark,14,21,.62,speckles=False)
        title=self.label(header,"TOMATO",size=10,color="red",weight="bold",cursor="fleur")
        title.pack(side="left",padx=(4,0))
        self.btn(header,"×",self.close,width=28,height=28,fill="white",fg="muted",size=15).pack(side="right")
        self.btn(header,"↗",self.toggle_mini,width=30,height=28,fill="white",fg="muted",size=13).pack(side="right",padx=(0,1))
        self.btn(header,"☾" if self.settings["theme"] == "light" else "☀",
                 self.toggle_theme,width=27,height=28,fill="surface",fg="text",size=11).pack(side="right",padx=(0,3))
        self.mini_pin=self.btn(header,"고정",self.toggle_pin,width=43,height=27,
                              fill="red_pale",fg="red",size=9)
        self.mini_pin.pack(side="right",padx=(0,3))
        for widget in (header,title,mark):
            widget.bind("<ButtonPress-1>",self.start_drag)
            widget.bind("<B1-Motion>",self.drag)
            widget.bind("<ButtonRelease-1>",self.end_drag)
        self.build_timer(panel,mini=True)
        self.mini_task_label=self.label(panel,"",size=9,color="muted",anchor="center")
        self.mini_task_label.pack(fill="x",pady=(4,0))
        self.mini_meeting_label = self.label(panel, "", size=9, color="red", anchor="center", cursor="hand2")
        self.mini_meeting_label.pack(fill="x", pady=(4,0))
        self.mini_meeting_label.bind("<Button-1>", self.open_meetings)

    def build_timer(self, parent,mini):
        modebar=tk.Frame(parent,bg=parent.cget("bg"))
        modebar.pack(fill="x",pady=(0,5 if mini else 7))
        for key,text in (("focus","집중"),("short","짧은 휴식"),("long","긴 휴식")):
            button=self.btn(modebar,text,lambda k=key:self.switch_mode(k),
                            width=82 if mini else 122,height=30 if mini else 35,
                            fill="surface" if key=="focus" else "white",
                            fg="red" if key=="focus" else "muted",size=9)
            button.pack(side="left",expand=True,fill="x",padx=(0,4) if key!="long" else 0)
            self.mode_buttons[key]=button
        if not mini:
            self.label(parent,"POMODORO TIMER",size=9,color="orange",weight="bold").pack(anchor="center",pady=(2,0))
        self.scene=tk.Canvas(parent,width=275 if mini else 380,height=106 if mini else 135,
                             bg=parent.cget("bg"),bd=0,highlightthickness=0)
        self.scene.pack(pady=(1 if mini else 4,0))
        self.scene.bind("<Configure>",lambda e:draw_tomato_scene(self.scene,self.mode))
        self.timer_label=self.label(parent,"25:00",size=48 if mini else 61,weight="bold")
        self.timer_label.pack(anchor="center",pady=(0,0))
        self.cycle_canvas=tk.Canvas(parent,width=210,height=31 if mini else 38,
                                    bg=parent.cget("bg"),bd=0,highlightthickness=0)
        self.cycle_canvas.pack(pady=(0,1 if mini else 5))
        self.cycle_canvas.bind("<Configure>",lambda e:self.draw_cycles())
        if not mini:
            self.label(parent,"현재 작업",size=9,color="hint").pack(pady=(0,2))
        if not mini:
            self.current_task=self.label(parent,"할 일 목록에서 작업을 선택해 주세요",size=10,color="muted",anchor="center")
            self.current_task.pack(fill="x",pady=(0,13))
        bar=tk.Frame(parent,bg=parent.cget("bg"))
        bar.pack(fill="x",pady=(3,0))
        self.btn(bar,"↻",self.reset_timer,width=44 if mini else 58,height=43 if mini else 48,
                 fill="gray_btn",fg="muted",size=19).pack(side="left")
        self.primary_button=self.btn(bar,"▶  시작",self.toggle_timer,width=160,
                                     height=43 if mini else 48,fill="red",fg="on_accent",size=12)
        self.primary_button.pack(side="left",fill="x",expand=True,padx=9)
        self.btn(bar,"≫",self.skip_timer,width=44 if mini else 58,height=43 if mini else 48,
                 fill="gray_btn",fg="muted",size=16).pack(side="left")
        if not mini:
            self.label(parent,"집중을 마치면 토마토가 쌓여요  ·  건너뛰기는 제외",
                       color="hint",size=9).pack(pady=(8,0))

    def draw_cycles(self):
        cv=self.cycle_canvas
        if cv is None:return
        cv.delete("all")
        total=self.settings["long_every"]
        w=max(210,int(cv.winfo_width()))
        # Show first eight tomato stamps, but keep all rounds accurately labeled.
        show=min(8,total)
        gap=min(42, max(23,(w-22)/max(1,show)))
        left=w/2-gap*(show-1)/2
        cv_h = max(31,int(cv.winfo_height()))
        center_y = min(26, cv_h-11)
        tomato_scale = 0.61 if cv_h>=38 else 0.53
        for i in range(show):
            draw_tomato(cv,left+i*gap,center_y,tomato_scale,
                        outline=i>=self.focus_cycle,speckles=False)
        if total>8:
            cv.create_text(w-4,center_y,text=f"/{total}",fill=P["muted"],anchor="e",font=(self.font_name,9))

    def build_tasks(self,parent):
        h=tk.Frame(parent,bg=P["white"])
        h.pack(fill="x",pady=(0,5))
        self.label(h,"오늘의 To-do",size=17,weight="bold").pack(side="left")
        self.task_count=self.label(h,"",size=9,color="muted")
        self.task_count.pack(side="right")
        self.label(parent,"하나의 할 일을 선택하고 토마토 한 개씩 쌓아보세요.",size=10,color="muted").pack(anchor="w",pady=(0,15))
        row=tk.Frame(parent,bg=P["white"])
        row.pack(fill="x",pady=(0,13))
        wrap=tk.Frame(row,bg=P["bg"],highlightthickness=1,highlightbackground=P["line"])
        wrap.pack(side="left",fill="x",expand=True,ipady=6)
        self.entry=tk.Entry(wrap,fg=P["text"],bg=P["bg"],insertbackground=P["red"],
                            relief="flat",bd=0,font=(self.font_name,10))
        self.entry.pack(fill="x",padx=12,pady=5)
        self.entry.insert(0,"할 일을 입력해 주세요")
        self.entry.config(fg=P["hint"])
        self.entry.bind("<FocusIn>",self.entry_focus)
        self.entry.bind("<FocusOut>",self.entry_blur)
        self.entry.bind("<Return>",lambda e:self.add_task())
        self.btn(row,"+ 추가",self.add_task,width=84,height=40,fill="red",fg="on_accent").pack(side="left",padx=(8,0))
        filters=tk.Frame(parent,bg=P["white"])
        filters.pack(fill="x",pady=(0,7))
        self.task_filter_buttons={}
        for key,text in (("all","전체"),("active","진행 중"),("done","완료")):
            b=self.btn(filters,text,lambda x=key:self.filter_tasks(x),width=71,height=30,
                       fill="red_pale" if key==self.filter_name else "white",
                       fg="red" if key==self.filter_name else "muted",size=9)
            b.pack(side="left",padx=(0,4))
            self.task_filter_buttons[key]=b
        list_host=tk.Frame(parent,bg=P["white"])
        list_host.pack(fill="both",expand=True)
        self.task_scroll=tk.Canvas(list_host,bg=P["white"],highlightthickness=0,bd=0)
        scroll=tk.Scrollbar(list_host,orient="vertical",command=self.task_scroll.yview,width=8)
        self.task_scroll.configure(yscrollcommand=scroll.set)
        self.task_scroll.pack(side="left",fill="both",expand=True)
        scroll.pack(side="right",fill="y")
        self.task_area=tk.Frame(self.task_scroll,bg=P["white"])
        self.scroll_window=self.task_scroll.create_window((0,0),window=self.task_area,anchor="nw")
        self.task_area.bind("<Configure>",lambda e:self.task_scroll.configure(scrollregion=self.task_scroll.bbox("all")))
        self.task_scroll.bind("<Configure>",lambda e:self.task_scroll.itemconfig(self.scroll_window,width=e.width))
        self.task_scroll.bind("<MouseWheel>",self.mouse_scroll)
        self.task_scroll.bind("<Button-4>",lambda e:self.task_scroll.yview_scroll(-1,"units"))
        self.task_scroll.bind("<Button-5>",lambda e:self.task_scroll.yview_scroll(1,"units"))
        self.label(parent,"✓ 완료    ·    제목 클릭 → 현재 작업으로 선택    ·    ★ 중요",
                   size=9,color="hint").pack(anchor="w",pady=(13,0))

    def entry_focus(self, _e=None):
        if self.entry and self.entry.get()=="할 일을 입력해 주세요":
            self.entry.delete(0,"end")
            self.entry.configure(fg=P["text"])

    def entry_blur(self, _e=None):
        if self.entry and not self.entry.get().strip():
            self.entry.insert(0,"할 일을 입력해 주세요")
            self.entry.configure(fg=P["hint"])

    def task_prediction(self, title, category):
        matches = []
        for t in self.state['tasks']:
            if not t.get('done') or not self._task_seconds.get(t.get('id')): continue
            if t.get('tracking_incomplete'): continue
            ratio = SequenceMatcher(None, title.casefold().strip(), str(t.get('title','')).casefold().strip()).ratio()
            if ratio >= .65 or (category.strip() and category.casefold().strip() == str(t.get('category','')).casefold().strip()):
                matches.append(self._task_seconds[t['id']]/60)
        return (round(median(matches)), len(matches)) if matches else (0,0)

    def task_info(self, t):
        actual = self._task_seconds.get(t.get('id'),0)/60
        est = self.mins(t.get('estimate_minutes'))
        text = f"실제 {actual:.1f}분"
        if est:
            diff = actual-est
            text += f" / 예상 {est}분 · " + (f"{abs(diff):.1f}분 초과" if diff>0 else (f"{abs(diff):.1f}분 단축" if t.get('done') else f"{abs(diff):.1f}분 여유"))
        return text

    def add_task(self):
        if not self.entry:return
        title=self.entry.get().strip()
        if not title or title=="할 일을 입력해 주세요": return
        if len(title)>180:
            messagebox.showwarning("할 일 추가","할 일은 180자 이하로 입력해 주세요.",parent=self.root)
            return
        category = simpledialog.askstring("업무 분류", "업무 카테고리 (예: 보고서, 개발, 분석)", parent=self.root)
        if category is None: return
        predicted, count = self.task_prediction(title, category)
        hint = f"\n유사 업무 {count}건의 중앙값: {predicted}분" if count else "\n추천에 필요한 완료 기록이 아직 없습니다."
        estimate = simpledialog.askinteger("예상 소요 시간", "예상 집중 시간 (분)"+hint, initialvalue=max(1,predicted or 25), minvalue=1, maxvalue=100000, parent=self.root)
        if estimate is None: return
        self.state["tasks"].insert(0,{"id":uuid.uuid4().hex[:12],"title":title,"done":False,
                                       "priority":False,"created_at":date.today().isoformat(),
                                       "completed_on":None,"category":category.strip(),"estimate_minutes":estimate})
        self.entry.delete(0,"end")
        self.entry_blur()
        self.root.focus_set()
        self.filter_name="all"
        self.save()
        self.refresh()

    def get_task(self, task_id):
        return next((t for t in self.state["tasks"] if t.get("id")==task_id),None)

    def toggle_task(self,task_id):
        t=self.get_task(task_id)
        if not t:return
        if self.session_started and self.mode == "focus" and self.session_task == task_id:
            self.record_partial()
            self.reset_timer()
        t["done"]=not t.get("done",False)
        t["completed_on"]=date.today().isoformat() if t["done"] else None
        if t["done"]:
            self.state["task_completion_log"].append({"date":t["completed_on"],"task_id":task_id,
                "estimate_minutes":self.mins(t.get("estimate_minutes")),"seconds":self._task_seconds.get(task_id,0)})
        else:
            self.state["task_completion_log"]=[r for r in self.state["task_completion_log"] if r.get("task_id")!=task_id or r.get("date")!=date.today().isoformat()]
        if t["done"] and self.active_task==task_id:self.active_task=None
        self.save();self.refresh()

    def priority_task(self,task_id):
        t=self.get_task(task_id)
        if t:t["priority"]=not t.get("priority",False);self.save();self.render_tasks()

    def choose_task(self,task_id):
        t=self.get_task(task_id)
        if self.mode == "focus" and self.session_started:
            messagebox.showinfo("집중 중", "현재 세션을 완료하거나 초기화한 뒤 선택해 주세요.", parent=self.root); return
        if t and not t.get("done"):
            self.active_task = None if self.active_task==task_id else task_id
            self.save();self.refresh()

    def delete_task(self,task_id):
        if self.session_started and self.session_task == task_id: return
        self.state["tasks"]=[t for t in self.state["tasks"] if t.get("id")!=task_id]
        if self.active_task==task_id:self.active_task=None
        self.save();self.refresh()

    def filter_tasks(self,val):
        self.filter_name=val
        self.render_tasks()

    def mouse_scroll(self,event):
        if self.task_scroll:
            self.task_scroll.yview_scroll(-1 if event.delta>0 else 1,"units")

    def render_tasks(self):
        if self.task_area is None:return
        # Rebuild only when task data, selection or filter actually changes.
        key=(self.filter_name, self.active_task, tuple(
            (t.get("id"), t.get("title"), bool(t.get("done")), bool(t.get("priority")), self._task_seconds.get(t.get("id"),0), t.get("estimate_minutes"))
            for t in self.state["tasks"]))
        if key == self._task_render_key:return
        # Normalize legacy estimates before sorting or clearing the visible list.
        items=sorted(self.state["tasks"],key=lambda t:(bool(t.get("done")),not bool(t.get("priority")), self.mins(self._task_seconds.get(t.get("id"),0)), self.mins(t.get("estimate_minutes"))))
        if self.filter_name=="active":items=[x for x in items if not x.get("done")]
        if self.filter_name=="done":items=[x for x in items if x.get("done")]
        self._task_render_key=None
        for child in self.task_area.winfo_children():child.destroy()
        for filter_key,button in self.task_filter_buttons.items():
            on=filter_key==self.filter_name
            button.set(fill="red_pale" if on else "white",fg="red" if on else "muted")
        self.task_count.configure(text=f"{sum(not x.get('done') for x in self.state['tasks'])}개 진행 중")
        if not items:
            self.label(self.task_area,"할 일이 없어요. 첫 번째 토마토를 심어볼까요?",size=10,color="muted").pack(pady=35)
            self.task_scroll.configure(scrollregion=self.task_scroll.bbox("all"))
            self._task_render_key=key
            return
        for t in items:
            tid=t.get("id")
            active=self.active_task==tid
            done=bool(t.get("done"))
            bg=P["red_pale"] if active else P["bg"]
            r=tk.Frame(self.task_area,bg=bg,padx=6,pady=7,highlightthickness=1,
                       highlightbackground=P["orange"] if active else P["line"])
            r.pack(fill="x",pady=(0,7),padx=(0,4))
            self.btn(r,"✓" if done else "○",lambda i=tid:self.toggle_task(i),
                     width=35,height=31,fill=bg,fg="green" if done else "muted",size=14).pack(side="left")
            text=self.label(r,t.get("title","제목 없음")+"\n"+self.task_info(t),size=10,color="hint" if done else "text",
                            bg=bg,anchor="w",cursor="hand2")
            text.pack(side="left",fill="x",expand=True,padx=(3,1))
            if done:
                text.config(font=self.done_font)
            text.bind("<Button-1>",lambda e,i=tid:self.choose_task(i))
            self.btn(r,"★" if t.get("priority") else "☆",lambda i=tid:self.priority_task(i),
                     width=30,height=31,fill=bg,fg="orange" if t.get("priority") else "hint",size=12).pack(side="right")
            self.btn(r,"×",lambda i=tid:self.delete_task(i),width=27,height=31,
                     fill=bg,fg="hint",size=13).pack(side="right")
            for widget in (r,*r.winfo_children()):
                widget.bind("<MouseWheel>",self.mouse_scroll)
        self.task_area.update_idletasks()
        self.task_scroll.configure(scrollregion=self.task_scroll.bbox("all"))
        self._task_render_key=key

    def active_task_title(self):
        obj=self.get_task(self.active_task)
        return str(obj.get("title","")) if obj else ""

    @staticmethod
    def mins(value):
        try:
            return max(0,int(value))
        except (ValueError,TypeError,OverflowError):
            return 0

    def _index_session(self, session):
        """One small aggregate per calendar day; no repeated full-history scan."""
        key = session.get("date")
        try:
            date.fromisoformat(key)
        except (ValueError, TypeError):
            return
        agg = self._daily_stats.setdefault(key, [0, 0, 0, 0])
        tid = session.get("task_id")
        seconds = self.mins(session.get("seconds", self.mins(session.get("minutes"))*60))
        if tid: self._task_seconds[tid] = self._task_seconds.get(tid,0)+seconds
        if session.get("partial"): return
        agg[0] += self.mins(session.get("minutes", 0))
        agg[1] += 1
        if type(session.get("pause_count")) is int:
            agg[2] += 1
            agg[3] += int(session["pause_count"] == 0)
        self._session_revision += 1
        self._stats_cache = None

    def date_totals(self):
        return {day: agg[0] for day, agg in self._daily_stats.items()}

    def today_totals(self):
        agg = self._daily_stats.get(date.today().isoformat(), (0, 0, 0, 0))
        return agg[0], agg[1]

    def daily_advice(self, today=None):
        yesterday=((today or date.today())-timedelta(days=1)).isoformat()
        records=[r for r in self.state.get("task_completion_log",[]) if r.get("date")==yesterday]
        ids={r.get("task_id") for r in records}
        records += [{"task_id":t.get("id"),"estimate_minutes":t.get("estimate_minutes"),"seconds":self._task_seconds.get(t.get("id"),0)} for t in self.state["tasks"] if t.get("completed_on")==yesterday and t.get("id") not in ids]
        comparable=[r for r in records if self.mins(r.get("estimate_minutes")) and self.mins(r.get("seconds"))]
        early=sum(self.mins(r.get("seconds")) < self.mins(r.get("estimate_minutes"))*60 for r in comparable)
        late=sum(self.mins(r.get("seconds")) > self.mins(r.get("estimate_minutes"))*60 for r in comparable)
        focus=sum(self.mins(r.get("seconds",self.mins(r.get("minutes"))*60)) for r in self.state["sessions"] if r.get("date")==yesterday and r.get("mode","focus")=="focus")
        breaks=[r for r in self.state.get("breaks",[]) if r.get("date")==yesterday]
        rest=sum(self.mins(r.get("seconds")) for r in breaks)
        if not (records or focus or breaks): return "어제 기록이 없어요. 오늘은 중요한 업무 하나를 선택하고 예상 시간을 설정해 보세요."
        summary=f"완료 {len(records)}건 · 조기 {early}건 · 초과 {late}건 · 집중 {focus/60:.0f}분 · 휴식 "+(f"{rest/60:.0f}분" if breaks else "기록 없음")
        if late and late>=early:
            ratios=[self.mins(r.get("seconds"))/(60*self.mins(r.get("estimate_minutes"))) for r in comparable if self.mins(r.get("seconds"))>60*self.mins(r.get("estimate_minutes"))]
            extra=min(100,max(10,round((median(ratios)-1)*100)))
            tip=f"비슷한 업무에는 예상 시간을 약 {extra}% 넉넉히 잡고, 큰 업무는 작은 단계로 나눠 보세요."
        elif early: tip="예상보다 빠르게 끝낸 업무가 있어요. 유사 업무의 예상 시간을 실제 기록에 맞춰 조정해 보세요."
        elif not records: tip="오늘은 진행 중인 중요한 업무 하나를 먼저 완료해 보세요."
        else: tip="오늘도 예상 시간과 실제 시간을 비교하며 업무를 진행해 보세요."
        if focus and not breaks: tip += " 휴식 기록이 없어 오늘은 휴식 타이머도 사용해 보세요."
        elif focus and rest/focus < 0.15: tip += " 기록상 휴식이 짧았으니 세션 사이에 충분히 쉬어 주세요."
        return summary+"\n"+tip

    def refresh(self):
        if getattr(self,"advice_label",None) is not None:
            day=date.today()
            if getattr(self,"_advice_day",None)!=day or getattr(self,"_advice_widget",None) is not self.advice_label:
                self.advice_label.config(text=self.daily_advice(day))
                self._advice_day=day
                self._advice_widget=self.advice_label
        if self.timer_label is not None:
            sec=max(0,int(self.remaining))
            self.timer_label.config(text=f"{sec//60:02d}:{sec%60:02d}")
        if self.primary_button is not None:
            self.primary_button.set(text="Ⅱ  잠시 멈춤" if self.running else "▶  시작")
        for key,b in self.mode_buttons.items():
            is_selected=key==self.mode
            b.set(fill="red_pale" if is_selected else "white",fg="red" if is_selected else "muted")
        if self.cycle_canvas is not None:self.draw_cycles()
        if self.scene is not None:draw_tomato_scene(self.scene,self.mode)
        if self.status_label is not None:self.status_label.config(text="●  "+self.status)
        if self.mini_task_label is not None:
            self.mini_task_label.config(text="집중할 일  ·  "+(self.active_task_title()[:18] or "미선택"))
        if self.mini_pin is not None:
            pinned=bool(self.settings["mini_always_on_top"])
            self.mini_pin.set(text="고정" if pinned else "해제",fill="red_pale" if pinned else "gray_btn",
                              fg="red" if pinned else "muted")
        if hasattr(self,"current_task") and self.current_task and self.current_task.winfo_exists() and not self.compact:
            self.current_task.configure(text=self.active_task_title() or "할 일 목록에서 작업을 선택해 주세요")
        if self.page=="focus" and not self.compact:
            mins, count=self.today_totals()
            summary={"minutes":mins,"sessions":count,
                     "tasks":sum(t.get("completed_on")==date.today().isoformat() for t in self.state["tasks"]),
                     "goal":min(100,round(mins/max(1,self.settings["daily_goal"])*100))}
            for key,label in self.summary_value.items():label.config(text=str(summary[key]))
            self.render_tasks()
        if self.page=="stats" and not self.compact:
            self.update_stats()
        self.update_meeting_summary()

    def toggle_timer(self):
        if self.running:self.pause_timer()
        else:self.start_timer()

    def start_timer(self):
        if self.running:return
        if self.pause_since is not None:
            self.pause_total += max(0,time.monotonic()-self.pause_since)
            self.pause_since=None
        if not self.session_started:
            self.session_started=True
            self.session_task=self.active_task if self.mode=="focus" else None
            self.session_seconds=0
            self.focus_started_at=datetime.now().isoformat(timespec="seconds")
        self.segment_started=time.monotonic()
        self.segment_budget=self.remaining
        self.running=True
        self.deadline=time.monotonic()+self.remaining
        self._schedule_tick()
        self.status="집중 중! 지금 하는 일 하나에만 마음을 모아요." if self.mode=="focus" else "휴식 중! 편하게 쉬어 가세요."
        self.refresh()

    def pause_timer(self):
        if not self.running:return
        self.capture_segment()
        self.remaining=max(0,math.ceil(self.deadline-time.monotonic()))
        self.running=False
        self.deadline=None
        self.pause_since=time.monotonic()
        if self.mode=="focus":self.pause_count+=1
        self.status="잠시 멈췄어요. 다시 이어서 할 수 있어요."
        self.refresh()

    def capture_segment(self):
        if self.segment_started is not None:
            self.session_seconds += min(self.segment_budget, max(0,time.monotonic()-self.segment_started))
            self.segment_started = None

    def record_break(self):
        if self.mode not in ("short", "long") or not self.session_started: return
        self.capture_segment()
        seconds=round(self.session_seconds)
        if seconds:
            self.state["breaks"].append({"date":date.today().isoformat(),"seconds":seconds,"mode":self.mode})
        self.session_seconds=0
        self.save()

    def record_partial(self):
        if self.mode != "focus":
            self.record_break()
            return
        if self.mode != "focus" or not self.session_started or not self.session_task: return
        self.capture_segment()
        seconds=round(self.session_seconds)
        if seconds:
            t=self.get_task(self.session_task)
            record={"date":date.today().isoformat(),"minutes":0,"seconds":seconds,"partial":True,"mode":"focus","task_id":self.session_task,"task_title":t.get("title","") if t else ""}
            self.state["sessions"].append(record); self._index_session(record)
        self.session_seconds=0
        self.save()

    def reset_session_meta(self):
        self.session_task=None
        self.segment_started=None
        self.session_seconds=0
        self.pause_count=0
        self.pause_total=0
        self.pause_since=None
        self.focus_started_at=None
        self.session_started=False

    def reset_timer(self):
        self.record_partial()
        self.running=False
        self.deadline=None
        self.remaining=60*self.settings[self.mode]
        self.reset_session_meta()
        self.status="타이머를 초기화했어요."
        self.refresh()

    def switch_mode(self,mode):
        if mode not in MODE_TITLE:return
        self.record_partial()
        self.mode=mode
        self.running=False
        self.deadline=None
        self.reset_session_meta()
        self.remaining=self.settings[mode]*60
        self.status=f"{MODE_TITLE[mode]} 준비 완료"
        self.refresh()

    def skip_timer(self):
        # A skipped focus session is not added to statistics.
        target="short" if self.mode=="focus" else "focus"
        self.switch_mode(target)
        self.status="다음 단계로 넘어갔어요. 완료 세션 통계에는 반영하지 않아요."
        self.refresh()

    def finish_session(self):
        self.capture_segment()
        old=self.mode
        self.running=False
        self.deadline=None
        if old=="focus":
            session = {
                "date":date.today().isoformat(),
                "minutes":self.settings["focus"],
                "mode":"focus",
                "task_id":self.session_task,
                "task_title":self.active_task_title(),
                "seconds":round(self.session_seconds),
                "started_at":self.focus_started_at,
                "finished_at":datetime.now().isoformat(timespec="seconds"),
                "pause_count":self.pause_count,
                "pause_seconds":round(self.pause_total),
            }
            self.state["sessions"].append(session)
            self._index_session(session)
            self.focus_cycle+=1
            if self.focus_cycle>=self.settings["long_every"]:
                self.focus_cycle=0
                self.mode="long"
            else:self.mode="short"
            self.status="토마토 수확 완료! 휴식할 시간이 왔어요."
        else:
            self.record_break()
            self.mode="focus"
            self.status="휴식 끝! 다시 한 번 시작해 볼까요?"
        self.reset_session_meta()
        self.remaining=self.settings[self.mode]*60
        self.save()
        try:self.root.bell()
        except tk.TclError:pass
        self.refresh()
        if old=="focus" and self.settings["auto_break"]:
            self.start_timer()
        if old=="focus":
            self.show_break_alert()

    def show_break_alert(self):
        """One persistent, non-modal celebration; animation stops after 2.4 seconds."""
        if self.break_popup is not None:
            self.break_popup.destroy()
        dlg = tk.Toplevel(self.root)
        self.break_popup = dlg
        dlg.title("Tomato Focus · 휴식 시간")
        dlg.configure(bg=P["bg"])
        dlg.resizable(False, False)
        dlg.attributes("-topmost", True)
        wrap = tk.Frame(dlg, bg=P["bg"], padx=22, pady=18)
        wrap.pack(fill="both", expand=True)
        cv = tk.Canvas(wrap, width=340, height=156, bg=P["bg"], highlightthickness=0)
        cv.pack()
        draw_tomato(cv, 170, 82, 2.0)
        self.label(wrap, "토마토 수확 완료!", size=20, weight="bold", color="red").pack(pady=(6, 4))
        self.label(wrap, "이제 잠깐 쉬어갈 시간이에요.", size=12).pack()
        mode = self.mode
        minutes = self.settings[mode]
        self.label(wrap, f"{'긴 휴식' if mode == 'long' else '짧은 휴식'} · {minutes}분", size=11, color="muted").pack(pady=10)
        job = None
        def cleanup(event=None):
            nonlocal job
            if event is not None and event.widget is not dlg: return
            if job is not None:
                try: self.root.after_cancel(job)
                except tk.TclError: pass
                job = None
            if self.break_popup is dlg: self.break_popup = None
        def dismiss(start=False):
            if start and self.mode == mode and not self.running:
                self.start_timer()
            cleanup()
            dlg.destroy()
        bar = tk.Frame(wrap, bg=P["bg"])
        bar.pack(fill="x", pady=(8, 0))
        self.btn(bar, "닫기", dismiss, width=150, border="line").pack(side="left", expand=True)
        self.btn(bar, "확인" if self.running else "휴식 시작", (dismiss if self.running else lambda: dismiss(True)), width=170, fill="red", fg="on_accent").pack(side="right", expand=True)
        dlg.protocol("WM_DELETE_WINDOW", dismiss)
        dlg.bind("<Escape>", lambda e: dismiss())
        dlg.bind("<Destroy>", cleanup, add="+")
        dlg.update_idletasks()
        w, h = dlg.winfo_reqwidth(), dlg.winfo_reqheight()
        dlg.geometry(f"{w}x{h}+{max(0,(dlg.winfo_screenwidth()-w)//2)}+{max(0,(dlg.winfo_screenheight()-h)//2)}")
        dlg.lift()
        rng = random.Random()
        particles = []
        for i in range(24):
            x = rng.choice((62, 278)); y = 105
            vx = rng.uniform(-65, 65); vy = rng.uniform(-145, -65)
            if i % 3 == 0:
                draw_tomato(cv, x, y, rng.uniform(.23,.38), speckles=False)
                # Tag the newly created tomato shapes as one moving particle.
                ids = cv.find_all()[-3:]
            else:
                color = rng.choice((P["red"], P["green"], "#F5B65D", "#F68B78"))
                ids = (cv.create_rectangle(x,y,x+5,y+9,fill=color,outline=""),)
            particles.append((ids,vx,vy))
        started = time.monotonic()
        last = 0.0
        def animate():
            nonlocal job, last
            job = None
            t = min(2.4, time.monotonic()-started)
            dt = t-last
            for ids,vx,vy in particles:
                for item in ids:
                    cv.move(item,vx*dt,vy*dt+85*(t*t-last*last))
            last = t
            if t < 2.4 and not self._closing:
                job = self.root.after(40, animate)
            else:
                for ids, _, _ in particles:
                    for item in ids: cv.delete(item)
                particles.clear()
        animate()

    def report_callback_exception(self, exc_type, exc_value, exc_traceback):
        LOGGER.error("Tk callback error", exc_info=(exc_type, exc_value, exc_traceback))

    def _cancel_after(self, attr):
        job = getattr(self, attr, None)
        setattr(self, attr, None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except tk.TclError:
                pass

    def _schedule_tick(self):
        self._cancel_after("_tick_after")
        if not self._closing:
            # Idle timer needs no 5 Hz polling. During focus the monotonic deadline
            # remains authoritative, so skipped UI frames do not lose elapsed time.
            self._tick_after = self.root.after(250 if self.running else 5000, self.tick)

    def tick(self):
        self._tick_after = None
        if self._closing:return
        try:
            today = date.today()
            if today != self._last_day:
                self._last_day = today
                self.refresh()
            if self.running and self.deadline is not None:
                new=max(0,math.ceil(self.deadline-time.monotonic()))
                if new!=self.remaining:
                    self.remaining=new
                    if self.timer_label is not None:
                        self.timer_label.config(text=f"{new//60:02d}:{new%60:02d}")
                if self.remaining==0:
                    self.finish_session()
        except Exception:
            LOGGER.exception("Timer tick failed; retrying")
        finally:
            # finish_session may start an automatic break and schedule a tick;
            # replacing the handle guarantees exactly one recurring timer.
            if not self._closing:
                self._schedule_tick()

    def switch_page(self,page):
        if self.compact or page==self.page:return
        self.page=page
        self.build()

    # ───── Meetings: local schedule and one-time reminders ─────
    @staticmethod
    def meeting_time(meeting):
        try:
            value = datetime.fromisoformat(meeting.get("start_at", ""))
            return value if value.tzinfo is None else None
        except (TypeError, ValueError):
            return None

    def upcoming_meetings(self, now=None):
        now = now or datetime.now()
        upcoming = []
        for m in self.state["meetings"]:
            start = self.meeting_time(m)
            if start is not None and start >= now:
                upcoming.append((start, m))
        upcoming.sort(key=lambda pair: pair[0])
        return [m for _, m in upcoming]

    def build_meetings(self, shell):
        hero = tk.Frame(shell, bg=P["bg"])
        hero.pack(fill="x", pady=(0, 13))
        left = tk.Frame(hero, bg=P["bg"])
        left.pack(side="left")
        self.label(left, "다가오는 회의", size=20, weight="bold").pack(anchor="w")
        self.label(left, "집중은 그대로, 회의 시작은 놓치지 않도록.", size=10, color="muted").pack(anchor="w", pady=(3, 0))
        self.btn(hero, "+ 회의 추가", lambda: self.meeting_dialog(), width=125, height=42,
                 fill="red", fg="on_accent", hover="red_dark").pack(side="right")
        summary = WhiteCard(shell, padding=16, bg="surface")
        summary.pack(fill="x", pady=(0, 12))
        self.label(summary.body, "NEXT MEETING", size=10, color="red", weight="bold").pack(anchor="w")
        self.meeting_next = self.label(summary.body, "", size=18, weight="bold", anchor="w", justify="left", wraplength=710)
        self.meeting_next.pack(fill="x", pady=(4, 3))
        self.meeting_next_detail = self.label(summary.body, "", size=10, color="muted", anchor="w")
        self.meeting_next_detail.pack(fill="x")
        card = WhiteCard(shell, padding=15)
        card.pack(fill="both", expand=True)
        header = tk.Frame(card.body, bg=P["white"])
        header.pack(fill="x", pady=(0, 10))
        self.label(header, "회의 일정", size=13, weight="bold").pack(side="left")
        self.meeting_filter_buttons = {}
        for key, caption in (("upcoming", "예정"), ("all", "전체")):
            button = self.btn(header, caption, lambda k=key: self.set_meeting_filter(k),
                              width=65, height=31, fill="surface", size=9)
            button.pack(side="right", padx=(5, 0))
            self.meeting_filter_buttons[key] = button
        area = tk.Frame(card.body, bg=P["white"])
        area.pack(fill="both", expand=True)
        canvas = tk.Canvas(area, bg=P["white"], highlightthickness=0, bd=0)
        scroll = tk.Scrollbar(area, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=scroll.set)
        scroll.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        self.meeting_list = tk.Frame(canvas, bg=P["white"])
        item = canvas.create_window((0, 0), window=self.meeting_list, anchor="nw")
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(item, width=e.width))
        self.meeting_list.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        self.meeting_canvas = canvas
        def wheel(e):
            if getattr(e, "num", 0) == 4: step = -1
            elif getattr(e, "num", 0) == 5: step = 1
            else: step = -1 if e.delta > 0 else 1
            canvas.yview_scroll(step, "units")
            return "break"
        self.meeting_wheel = wheel
        for widget in (canvas, self.meeting_list):
            for event in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(event, wheel)
        self.render_meetings()
        self.label(shell, "알림은 Tomato Focus가 실행 중일 때 표시됩니다. 타이머는 자동 중단되지 않아요.",
                   size=9, color="muted").pack(anchor="w", pady=(10, 0))

    def set_meeting_filter(self, value):
        self.meeting_filter = value
        self.render_meetings()

    def render_meetings(self):
        if self.meeting_list is None or not self.meeting_list.winfo_exists(): return
        now = datetime.now()
        for key, btn in self.meeting_filter_buttons.items():
            active = key == self.meeting_filter
            btn.set(fill="red_pale" if active else "surface", fg="red" if active else "muted")
        for item in self.meeting_list.winfo_children(): item.destroy()
        meetings = self.upcoming_meetings(now)
        if self.meeting_filter == "all":
            past = sorted((m for m in self.state["meetings"] if self.meeting_time(m) and self.meeting_time(m) < now),
                          key=self.meeting_time, reverse=True)
            meetings += past
        if not meetings:
            self.label(self.meeting_list, "등록된 회의가 없어요. + 회의 추가로 일정을 등록하세요.",
                       size=11, color="muted").pack(pady=45)
        for m in meetings:
            dt = self.meeting_time(m)
            row = tk.Frame(self.meeting_list, bg=P["white"], highlightbackground=P["line"], highlightthickness=1, padx=13, pady=12)
            row.pack(fill="x", pady=(0, 8))
            stamp = tk.Frame(row, bg=P["surface"], padx=10, pady=6)
            stamp.pack(side="left", padx=(0, 13))
            self.label(stamp, f"{dt:%m.%d}", size=12, weight="bold", color="red").pack()
            self.label(stamp, f"{dt:%H:%M}", size=10, color="muted").pack()
            actions = tk.Frame(row, bg=P["white"])
            actions.pack(side="right")
            self.btn(actions, "수정", lambda item=m: self.meeting_dialog(item), width=56, height=31, fill="surface", size=9).pack(side="left", padx=(0, 5))
            self.btn(actions, "삭제", lambda item=m: self.delete_meeting(item), width=56, height=31, fill="white", fg="muted", border="line", size=9).pack(side="left")
            info = tk.Frame(row, bg=P["white"])
            info.pack(side="left", fill="x", expand=True)
            title = m["title"]
            self.label(info, title if len(title) <= 42 else title[:41]+"…", size=12, weight="bold", anchor="w").pack(fill="x")
            status = "시작 시간 경과" if dt < now else ("알림 표시 완료" if m.get("notified") else "알림 예정")
            self.label(info, f"{dt:%Y.%m.%d} ({DAY_KO[dt.weekday()]})  ·  {m['remind_minutes']}분 전  ·  {status}",
                       size=9, color="muted", anchor="w").pack(fill="x", pady=(3, 0))
            for widget in (row, stamp, info, actions, *stamp.winfo_children(), *info.winfo_children()):
                for event in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                    widget.bind(event, self.meeting_wheel)
        self.meeting_view_key = (now.date(), tuple(m["id"] for m in self.upcoming_meetings(now)))
        self.update_meeting_summary(now)

    def update_meeting_summary(self, now=None, meetings=None):
        if self.meeting_next is None and self.mini_meeting_label is None:return
        now = now or datetime.now()
        if meetings is None:
            meetings = self.upcoming_meetings(now)
        if meetings:
            m = meetings[0]
            dt = self.meeting_time(m)
            minutes = max(0, math.ceil((dt-now).total_seconds()/60))
            left = (f"{minutes}분 후" if minutes < 60 else
                    f"{minutes//60}시간 {minutes%60}분 후" if minutes < 1440 else f"{minutes//1440}일 후")
            headline = m["title"]
            detail = f"{dt:%m.%d} ({DAY_KO[dt.weekday()]}) {dt:%H:%M}  ·  {left}  ·  {m['remind_minutes']}분 전 알림"
            mini = f"회의 {dt:%H:%M} · {left} · {headline[:12]}" if dt.date() == now.date() else f"다음 회의 {dt:%m.%d %H:%M}"
        else:
            headline, detail, mini = "예정된 회의 없음", "새 일정을 추가하면 시작 전에 알려드려요.", "예정된 회의 없음"
        key = (headline, detail, mini)
        if key == self._meeting_summary_key:return
        self._meeting_summary_key = key
        if self.meeting_next is not None:
            self.meeting_next.configure(text=headline)
            self.meeting_next_detail.configure(text=detail)
        if self.mini_meeting_label is not None:
            self.mini_meeting_label.configure(text=mini)

    def open_meetings(self, _event=None):
        if self.compact: self.toggle_mini()
        self.switch_page("meetings")
        return "break"

    def meeting_dialog(self, meeting=None):
        dlg = tk.Toplevel(self.root)
        dlg.title("Tomato Focus · 회의 " + ("수정" if meeting else "추가"))
        dlg.configure(bg=P["bg"])
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()
        wrap = tk.Frame(dlg, bg=P["bg"], padx=22, pady=20)
        wrap.pack(fill="both", expand=True)
        self.label(wrap, "회의 수정" if meeting else "새 회의 등록", size=17, weight="bold").pack(anchor="w")
        self.label(wrap, "회의 시작 전에 토마토가 알려드려요.", size=10, color="muted").pack(anchor="w", pady=(3, 15))
        dt = self.meeting_time(meeting) if meeting else (datetime.now() + timedelta(minutes=30)).replace(second=0, microsecond=0)
        values = {"title": tk.StringVar(value=meeting["title"] if meeting else ""),
                  "date": tk.StringVar(value=dt.strftime("%Y-%m-%d")),
                  "time": tk.StringVar(value=dt.strftime("%H:%M"))}
        widgets = {}
        for key, cap in (("title", "회의 제목"), ("date", "날짜 (YYYY-MM-DD)"), ("time", "시작 시간 (24시간제 HH:MM)")):
            self.label(wrap, cap, size=10, weight="bold").pack(anchor="w", pady=(0, 4))
            entry = tk.Entry(wrap, textvariable=values[key], width=37, bg=P["white"], fg=P["text"], insertbackground=P["red"],
                             font=(self.font_name, 11), relief="solid", bd=1, highlightbackground=P["line"])
            entry.pack(fill="x", ipady=7, pady=(0, 12))
            widgets[key] = entry
        self.label(wrap, "알림 시점", size=10, weight="bold").pack(anchor="w", pady=(0, 6))
        remind = tk.IntVar(value=meeting["remind_minutes"] if meeting else 10)
        options = tk.Frame(wrap, bg=P["bg"])
        options.pack(fill="x")
        buttons = {}
        def choose(n):
            remind.set(n)
            for k, button in buttons.items():
                button.set(fill="red_pale" if k==n else "white", fg="red" if k==n else "muted")
        for n in (10, 15):
            b = self.btn(options, f"{n}분 전", lambda v=n: choose(v), width=150, height=36, border="line")
            b.pack(side="left", fill="x", expand=True, padx=(0, 8) if n==10 else 0)
            buttons[n] = b
        choose(remind.get())
        feedback = self.label(wrap, "", size=9, color="red", wraplength=340, justify="left")
        feedback.pack(anchor="w", pady=(7, 4))
        def save_meeting():
            if not dlg.winfo_exists(): return
            title = values["title"].get().strip()
            if not title or len(title)>150:
                feedback.configure(text="회의 제목은 1~150자로 입력해 주세요."); return
            try:
                start = datetime.strptime(values["date"].get().strip()+" "+values["time"].get().strip(), "%Y-%m-%d %H:%M")
            except ValueError:
                feedback.configure(text="날짜와 시간을 확인해 주세요. 예: 2026-11-17 / 14:30"); return
            if start <= datetime.now():
                feedback.configure(text="현재보다 이후의 회의 시작 시간을 입력해 주세요."); return
            new_time = start.isoformat(timespec="minutes")
            old_notified = bool(meeting and meeting.get("notified") and meeting.get("start_at")==new_time and meeting.get("remind_minutes")==remind.get())
            data = {"id": meeting["id"] if meeting else uuid.uuid4().hex, "title": title,
                    "start_at": new_time, "remind_minutes": remind.get(), "notified": old_notified}
            if meeting: meeting.update(data)
            else: self.state["meetings"].append(data)
            self.save()
            dlg.destroy()
            self.render_meetings()
            self.update_meeting_summary()
            self.check_meetings()
        self.btn(wrap, "회의 저장", save_meeting, width=318, height=42, fill="red", fg="on_accent", hover="red_dark").pack(fill="x", pady=(6, 0))
        dlg.bind("<Return>", lambda e: save_meeting())
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        widgets["title"].focus_set()

    def delete_meeting(self, meeting):
        if not messagebox.askyesno("회의 삭제", f"'{meeting['title']}' 일정을 삭제할까요?", parent=self.root): return
        self.state["meetings"] = [m for m in self.state["meetings"] if m["id"] != meeting["id"]]
        self.save()
        self.render_meetings()
        self.update_meeting_summary()

    def check_meetings(self, now=None, meetings=None):
        now = now or datetime.now()
        if meetings is None:
            meetings = self.upcoming_meetings(now)
        self.meeting_popups = [w for w in self.meeting_popups if w.winfo_exists()]
        changed = False
        # Each due meeting gets its own alert, even if an earlier one is still open.
        for meeting in meetings:
            start = self.meeting_time(meeting)
            if not meeting.get("notified") and start-timedelta(minutes=meeting["remind_minutes"]) <= now <= start:
                self.show_meeting_alert(meeting, now)
                meeting["notified"] = True
                changed = True
        if changed:
            self.save()
            self.render_meetings()

    def meeting_tick(self):
        self._meeting_after = None
        if self._closing:return
        try:
            now = datetime.now()
            meetings = self.upcoming_meetings(now)
            self.check_meetings(now, meetings)
            self.update_meeting_summary(now, meetings)
            if self.meeting_list is not None:
                key = (now.date(), tuple(m["id"] for m in meetings))
                if key != self.meeting_view_key:
                    self.render_meetings()
        except Exception:
            LOGGER.exception("Meeting tick failed; retrying")
        finally:
            if not self._closing:
                # Reminder resolution: at most ~5 seconds of polling latency
                # under normal load. No scanning/repainting five times a second.
                self._meeting_after = self.root.after(5000, self.meeting_tick)

    def show_meeting_alert(self, meeting, now):
        start = self.meeting_time(meeting)
        minutes = max(0, math.ceil((start-now).total_seconds()/60))
        dlg = tk.Toplevel(self.root)
        self.meeting_popups.append(dlg)
        dlg.title("Tomato Focus · 회의 알림")
        dlg.configure(bg=P["bg"])
        dlg.resizable(False, False)
        dlg.attributes("-topmost", True)
        # Standalone, non-modal alert so it can appear over another application.
        wrap = tk.Frame(dlg, bg=P["bg"], padx=20, pady=16)
        wrap.pack(fill="both", expand=True)
        head = tk.Frame(wrap, bg=P["bg"])
        head.pack(fill="x")
        icon = tk.Canvas(head, width=46, height=44, bg=P["bg"], highlightthickness=0)
        icon.pack(side="left", padx=(0, 8))
        draw_tomato(icon, 23, 27, 1.0)
        self.label(head, f"회의 {minutes}분 전" if minutes else "회의 시작 시간", size=15, weight="bold", color="red").pack(side="left")
        card = WhiteCard(wrap, padding=13)
        card.pack(fill="x", pady=(8, 10))
        self.label(card.body, meeting["title"], size=14, weight="bold", wraplength=320, justify="left", anchor="w").pack(fill="x")
        self.label(card.body, f"{start:%Y.%m.%d} ({DAY_KO[start.weekday()]})  {start:%H:%M} 시작", size=10, color="muted").pack(anchor="w", pady=(5, 0))
        self.label(wrap, "실행 중인 집중 타이머는 계속 진행됩니다.", size=9, color="muted").pack(anchor="w")
        bar = tk.Frame(wrap, bg=P["bg"])
        bar.pack(fill="x", pady=(12, 0))
        def dismiss(open_schedule=False):
            if dlg in self.meeting_popups: self.meeting_popups.remove(dlg)
            dlg.destroy()
            if open_schedule: self.open_meetings()
        self.btn(bar, "일정 보기", lambda: dismiss(True), width=145, height=38, fill="white", border="line").pack(side="left", fill="x", expand=True, padx=(0, 7))
        self.btn(bar, "확인", dismiss, width=145, height=38, fill="red", fg="on_accent").pack(side="left", fill="x", expand=True)
        dlg.protocol("WM_DELETE_WINDOW", dismiss)
        dlg.bind("<Escape>", lambda e: dismiss())
        dlg.update_idletasks()
        w, h = max(380, dlg.winfo_reqwidth()), dlg.winfo_reqheight()
        offset = 32 * ((len(self.meeting_popups)-1) % 8)
        x = max(0, dlg.winfo_screenwidth()-w-22-offset)
        y = max(0, dlg.winfo_screenheight()-h-72-offset)
        dlg.geometry(f"{w}x{h}+{x}+{y}")
        dlg.lift()
        try: self.root.bell()
        except tk.TclError: pass


    # ───── Stats: week/month/year, chart, and activity map ─────
    def period_bounds(self):
        day=self.anchor_day
        if self.period=="week":
            first=day-timedelta(days=day.weekday())
            return first,first+timedelta(days=6)
        if self.period=="month":
            first=day.replace(day=1)
            last=day.replace(day=calendar.monthrange(day.year,day.month)[1])
            return first,last
        return date(day.year,1,1),date(day.year,12,31)

    def period_days(self):
        start,end=self.period_bounds()
        return [start+timedelta(days=i) for i in range((end-start).days+1)]

    def period_change(self,period):
        if self.period==period:return
        self.period=period
        self.anchor_day=date.today()
        self.update_stats()

    def shift_period(self,direction):
        current=self.anchor_day
        if self.period=="week":
            self.anchor_day=current+timedelta(days=7*direction)
        elif self.period=="month":
            index=current.year*12+current.month-1+direction
            y,m=divmod(index,12)
            self.anchor_day=date(y,m+1,1)
        else:
            self.anchor_day=date(current.year+direction,1,1)
        self.update_stats()

    def period_to_today(self):
        self.anchor_day=date.today()
        self.update_stats()

    def build_statistics(self,shell):
        hero=tk.Frame(shell,bg=P["bg"])
        hero.pack(fill="x",pady=(0,13))
        left=tk.Frame(hero,bg=P["bg"])
        left.pack(side="left")
        self.label(left,"내 몰입의 발자국",size=20,weight="bold").pack(anchor="w")
        self.label(left,"완료한 토마토로 주·월·연 집중 패턴을 확인해요.",size=10,color="muted").pack(anchor="w",pady=(2,0))
        selector=tk.Frame(hero,bg=P["bg"])
        selector.pack(side="right")
        for key,text in (("week","주간"),("month","월간"),("year","연간")):
            b=self.btn(selector,text,lambda k=key:self.period_change(k),width=71,height=37,
                       fill="red_pale" if self.period==key else "white",
                       fg="red" if self.period==key else "muted",border="line" if self.period!=key else None)
            b.pack(side="left",padx=(0,5))
            self.period_buttons[key]=b
        periodbar=tk.Frame(shell,bg=P["bg"])
        periodbar.pack(fill="x",pady=(0,12))
        self.btn(periodbar,"‹",lambda:self.shift_period(-1),width=34,height=32,fill="white",border="line",size=15).pack(side="left")
        self.period_caption=self.label(periodbar,"",size=13,weight="bold")
        self.period_caption.pack(side="left",padx=14)
        self.btn(periodbar,"›",lambda:self.shift_period(1),width=34,height=32,fill="white",border="line",size=15).pack(side="left")
        self.btn(periodbar,"오늘",self.period_to_today,width=64,height=32,fill="white",border="line",size=9).pack(side="right")
        summary=tk.Frame(shell,bg=P["bg"],height=100)
        summary.pack(fill="x",pady=(0,12))
        summary.pack_propagate(False)
        for i,(key,cap,unit) in enumerate((("total","누적 몰입","분"),("count","완료한 토마토","개"),
                                         ("days","몰입한 날","일"),("clean","끊김 없는 집중","%"))):
            c=WhiteCard(summary,padding=12)
            c.pack(side="left",fill="both",expand=True,padx=(0,9) if i<3 else 0)
            self.label(c.body,cap,size=10,color="muted").pack(anchor="w")
            r=tk.Frame(c.body,bg=P["white"])
            r.pack(anchor="w",pady=(6,0))
            val=self.label(r,"—",size=20,weight="bold",color="red" if i==0 else "text")
            val.pack(side="left")
            self.label(r,unit,size=10,color="muted").pack(side="left",padx=(4,0),pady=(5,0))
            self.stats_summary[key]=val
        top_card=WhiteCard(shell,padding=14)
        top_card.pack(fill="both",expand=True,pady=(0,12))
        heading=tk.Frame(top_card.body,bg=P["white"])
        heading.pack(fill="x")
        self.label(heading,"몰입 시간 분포",size=13,weight="bold").pack(side="left")
        self.label(heading,"진한 토마토색 = 많이 몰입한 시간",size=9,color="muted").pack(side="right")
        self.chart_canvas=tk.Canvas(top_card.body,bg=P["white"],height=150,highlightthickness=0)
        self.chart_canvas.pack(fill="both",expand=True,pady=(5,0))
        self.chart_canvas.bind("<Configure>",lambda e:self.draw_bar_chart())
        bottom=WhiteCard(shell,padding=13)
        bottom.pack(fill="x")
        head=tk.Frame(bottom.body,bg=P["white"])
        head.pack(fill="x")
        self.label(head,"Activity Map  ·  몰입 잔디",size=13,weight="bold").pack(side="left")
        self.label(head,"연한색 → 진한색  ·  날짜별 집중 시간",size=9,color="muted").pack(side="right")
        self.heat_canvas=tk.Canvas(bottom.body,bg=P["white"],height=154,highlightthickness=0)
        self.heat_canvas.pack(fill="x",pady=(5,0))
        self.heat_canvas.bind("<Configure>",lambda e:self.draw_heatmap())
        self.stats_info=self.label(shell,"",size=10,color="muted")
        self.stats_info.pack(anchor="w",pady=(10,0))

    def stats_data(self):
        start, end = self.period_bounds()
        cache_key = (start, end, self._session_revision)
        if self._stats_cache is not None and self._stats_cache[0] == cache_key:
            return self._stats_cache[1]
        days = self.period_days()
        totals = {}
        count = known = clean_count = 0
        for day in days:
            key = day.isoformat()
            minutes, n, k, c = self._daily_stats.get(key, (0, 0, 0, 0))
            totals[key] = minutes
            count += n
            known += k
            clean_count += c
        vals = [totals[d.isoformat()] for d in days]
        clean = round(clean_count * 100 / known) if known else None
        result = (days, vals, count, clean, totals)
        self._stats_cache = (cache_key, result)
        return result

    def update_stats(self):
        if self.chart_canvas is None:return
        for name,b in self.period_buttons.items():
            active=name==self.period
            b.set(fill="red_pale" if active else "white",fg="red" if active else "muted")
        start,end=self.period_bounds()
        if self.period=="week":caption=f"{start:%Y.%m.%d}  —  {end:%m.%d}"
        elif self.period=="month":caption=f"{start:%Y년 %m월}"
        else:caption=f"{start.year}년"
        self.period_caption.configure(text=caption)
        days,vals,count,clean,_=self.stats_data()
        overview={"total":sum(vals),"count":count,"days":sum(x>0 for x in vals),
                  "clean":"—" if clean is None else clean}
        for key,label in self.stats_summary.items():label.config(text=str(overview[key]))
        if vals and max(vals)>0:
            ix=max(range(len(vals)),key=lambda i:vals[i])
            date_max=days[ix]
            if self.period=="year":
                by_month={i:0 for i in range(1,13)}
                for d,v in zip(days,vals):by_month[d.month]+=v
                strong_month=max(by_month,key=by_month.get)
                story=f"가장 몰입한 달은 {strong_month}월 · {by_month[strong_month]}분  |  "
            else:
                story=f"가장 몰입한 날은 {date_max:%m/%d} · {vals[ix]}분  |  "
            story+=f"기간 목표 달성일 {sum(v>=self.settings['daily_goal'] for v in vals)}일"
        else:story="아직 기록이 없어요. 타이머를 끝까지 완료하면 여기에 기록됩니다."
        self.stats_info.config(text=story+"  ·  과거 기록은 일시정지 정보가 없을 수 있어요.")
        self.draw_bar_chart();self.draw_heatmap()

    def draw_bar_chart(self):
        cv=self.chart_canvas
        if cv is None:return
        cv.delete("all")
        w=max(cv.winfo_width(),380)
        h=max(cv.winfo_height(),170)
        days,vals,_sessions,_clean,_totals=self.stats_data()
        if self.period=="year":
            buckets=[sum(v for d,v in zip(days,vals) if d.month==m) for m in range(1,13)]
            labels=[f"{m}월" for m in range(1,13)]
        else:
            buckets=vals
            if self.period=="week":labels=DAY_KO
            else:labels=[str(d.day) for d in days]
        if not buckets:return
        left,right,top,bottom=42,w-17,16,h-27
        chartheight=max(1,bottom-top)
        maximum=max(max(buckets),self.settings["daily_goal"] if self.period!="year" else 600,30)
        maximum=math.ceil(maximum/50)*50
        for q in range(4):
            y=bottom-(q/3)*chartheight
            cv.create_line(left,y,right,y,fill=P["line"],dash=(2,5))
            cv.create_text(left-9,y,text=str(round(maximum*q/3)),anchor="e",
                           fill=P["hint"],font=(self.font_name,8))
        if self.period!="year":
            goal_y=bottom-(self.settings["daily_goal"]/maximum)*chartheight
            cv.create_line(left,goal_y,right,goal_y,fill=P["orange"],dash=(5,4))
        count=len(buckets)
        slot=(right-left)/count
        width=min(48 if self.period=="week" else 25 if self.period=="year" else 15,slot*.64)
        today=date.today()
        for i,num in enumerate(buckets):
            x=left+(i+.5)*slot
            y=bottom-(num/maximum)*chartheight
            shade=P["red_dark"] if (self.period!="year" and days[i]==today) else (P["red"] if num>=self.settings["daily_goal"] else P["orange"])
            if num>0:
                rounded_rect(cv,x-width/2,y,x+width/2,bottom,min(6,width/2),fill=shade)
                if self.period in ("week","year"):
                    cv.create_text(x,max(10,y-9),text=str(num),fill=P["text"],
                                   font=(self.font_name,8,"bold"))
            show=(self.period!="month" or i==0 or (i+1)%5==0)
            if show:
                cv.create_text(x,bottom+13,text=labels[i],fill=P["muted"],font=(self.font_name,8))

    def draw_heatmap(self):
        cv=self.heat_canvas
        if cv is None:return
        cv.delete("all")
        w=max(340,cv.winfo_width())
        _days,_vals,_sessions,_clean,totals=self.stats_data()
        start,end=self.period_bounds()
        if self.period=="year":
            # GitHub-style 53-column calendar: each column is a week, Mon→Sun rows.
            jan1=date(start.year,1,1)
            monday=jan1-timedelta(days=jan1.weekday())
            cols=((end-monday).days//7)+1
            gap=3
            side=35
            square=max(6,min(15,(w-side-12-(cols-1)*gap)/cols))
            row_h=14
            cv.configure(height=145)
            for row in range(7):
                if row%2==0:cv.create_text(9,36+row*row_h,text=DAY_KO[row],anchor="w",fill=P["hint"],font=(self.font_name,8))
            last_month=None
            for idx in range(cols):
                week_start=monday+timedelta(days=7*idx)
                if week_start.month!=last_month and week_start.year==jan1.year:
                    cv.create_text(side+idx*(square+gap),11,text=f"{week_start.month}월",fill=P["muted"],anchor="w",font=(self.font_name,8))
                    last_month=week_start.month
                for wd in range(7):
                    d=week_start+timedelta(days=wd)
                    if d.year!=jan1.year:continue
                    x=side+idx*(square+gap)
                    y=30+wd*row_h
                    rounded_rect(cv,x,y,x+square,y+square,2,fill=solid_color(totals.get(d.isoformat(),0)))
        else:
            days=self.period_days()
            if self.period=="week":
                cv.configure(height=100)
                step=min(110,(w-30)/7)
                x0=(w-step*7)/2
                for i,d in enumerate(days):
                    x=x0+i*step
                    cv.create_text(x+step/2,14,text=DAY_KO[d.weekday()],fill=P["muted"],font=(self.font_name,9))
                    rounded_rect(cv,x+step/2-18,28,x+step/2+18,64,8,
                                 fill=solid_color(totals.get(d.isoformat(),0)))
                    cv.create_text(x+step/2,78,text=str(d.day),fill=P["text"],font=(self.font_name,9))
            else:
                cv.configure(height=141)
                start_weekday=start.weekday()
                step=min(66,(w-20)/7)
                x0=(w-step*7)/2
                for weekday,letter in enumerate(DAY_KO):
                    cv.create_text(x0+(weekday+.5)*step,12,text=letter,fill=P["muted"],font=(self.font_name,8))
                for d in days:
                    ix=start_weekday+d.day-1
                    c,r=ix%7,ix//7
                    cx=x0+(c+.5)*step
                    cy=22+r*19
                    rounded_rect(cv,cx-14,cy,cx+14,cy+17,5,fill=solid_color(totals.get(d.isoformat(),0)))
                    color="#FFFFFF" if totals.get(d.isoformat(),0)>=120 else P["text"]
                    cv.create_text(cx,cy+8.5,text=str(d.day),fill=color,font=(self.font_name,8))

    # ───── Settings, floating pin/drag and window lifetime ─────
    def settings_dialog(self):
        dlg=tk.Toplevel(self.root)
        dlg.title("Tomato Focus · 설정")
        dlg.geometry("435x690")
        dlg.resizable(False,False)
        dlg.configure(bg=P["bg"])
        dlg.transient(self.root)
        dlg.grab_set()
        wrap=tk.Frame(dlg,bg=P["bg"],padx=25,pady=23)
        wrap.pack(fill="both",expand=True)
        self.label(wrap,"나에게 맞는 몰입 설정",size=17,weight="bold").pack(anchor="w")
        self.label(wrap,"토마토의 크기보다, 오늘의 집중을 정해보세요.",size=10,color="muted").pack(anchor="w",pady=(4,15))
        fields=(("집중 시간 (분)","focus"),("짧은 휴식 (분)","short"),("긴 휴식 (분)","long"),
                ("긴 휴식까지 세션 수","long_every"),("하루 집중 목표 (분)","daily_goal"))
        inputs={}
        for title,key in fields:
            row=tk.Frame(wrap,bg=P["bg"])
            row.pack(fill="x",pady=5)
            self.label(row,title,size=10).pack(side="left")
            value=tk.StringVar(value=str(self.settings[key]))
            inputs[key]=value
            box=tk.Entry(row,textvariable=value,width=8,justify="center",font=(self.font_name,10),
                         bg=P["white"],fg=P["text"],insertbackground=P["red"],
                         relief="solid",bd=1,highlightbackground=P["line"])
            box.pack(side="right",ipady=4)
        self.label(wrap,"화면 테마",size=11,weight="bold").pack(anchor="w",pady=(13,6))
        chosen_theme=tk.StringVar(value=self.settings["theme"])
        theme_bar=tk.Frame(wrap,bg=P["bg"])
        theme_bar.pack(fill="x",pady=(0,4))
        theme_buttons={}
        def choose_theme(value):
            chosen_theme.set(value)
            for key,button in theme_buttons.items():
                selected=key==value
                button.set(fill="red_pale" if selected else "white",
                           fg="red" if selected else "muted")
        for key,text in (("light","☀  라이트"),("dark","☾  다크")):
            button=self.btn(theme_bar,text,lambda v=key:choose_theme(v),width=150,height=36,
                            fill="red_pale" if key==chosen_theme.get() else "white",
                            fg="red" if key==chosen_theme.get() else "muted",border="line")
            button.pack(side="left",fill="x",expand=True,padx=(0,8) if key=="light" else 0)
            theme_buttons[key]=button
        self.label(wrap,"메인 화면과 미니 위젯에 동일하게 적용됩니다.",size=9,color="hint").pack(anchor="w")
        self.label(wrap,"창 표시",size=11,weight="bold").pack(anchor="w",pady=(12,6))
        mini_pin=tk.BooleanVar(value=self.settings["mini_always_on_top"])
        main_pin=tk.BooleanVar(value=self.settings["always_on_top"])
        auto=tk.BooleanVar(value=self.settings["auto_break"])
        sleep=tk.BooleanVar(value=self.settings["prevent_sleep"])
        for name,var in (("미니 위젯을 다른 창보다 항상 위에 표시",mini_pin),
                         ("메인 대시보드도 항상 위에 표시",main_pin),
                         ("집중 완료 후 휴식 자동 시작",auto),
                         ("실행 중 PC 자동 절전 방지 (Windows)",sleep)):
            tk.Checkbutton(wrap,text=name,variable=var,fg=P["text"],bg=P["bg"],
                           activebackground=P["bg"],activeforeground=P["red"],
                           selectcolor=P["white"],font=(self.font_name,10),
                           highlightthickness=0).pack(anchor="w",pady=3)
        def apply():
            try:
                new={k:int(v.get()) for k,v in inputs.items()}
                if any(not 1<=x<=999 for x in new.values()) or new["long_every"]>20:
                    raise ValueError
            except ValueError:
                messagebox.showerror("설정 오류","시간은 1~999분, 세션 수는 1~20회로 입력해 주세요.",parent=dlg)
                return
            if self.running:self.pause_timer()
            elapsed=max(0,self.settings[self.mode]*60-self.remaining)
            self.settings.update(new)
            self.settings["mini_always_on_top"]=bool(mini_pin.get())
            self.settings["always_on_top"]=bool(main_pin.get())
            self.settings["auto_break"]=bool(auto.get())
            self.settings["prevent_sleep"]=bool(sleep.get())
            self.apply_sleep_policy()
            self.remaining=max(1,self.settings[self.mode]*60-elapsed)
            self.focus_cycle%=self.settings["long_every"]
            self.status="설정이 저장됐어요."
            dlg.destroy()
            self.set_theme(chosen_theme.get())
            self.apply_topmost()
            self.refresh()
        self.btn(wrap,"설정 저장",apply,width=360,height=44,fill="red",fg="on_accent",size=11).pack(fill="x",pady=(15,0))
        dlg.bind("<Return>",lambda e:apply())
        dlg.bind("<Escape>",lambda e:dlg.destroy())

    def set_theme(self, theme):
        """Change light/dark appearance, preserving timer, tasks and statistics state."""
        theme = theme if theme in THEMES else "light"
        was_changed = self.settings.get("theme") != theme
        self.settings["theme"] = theme
        apply_palette(theme)
        if was_changed:
            self.build()
            # Reassert the floating-widget stacking mode after reconfiguring its frame.
            self._schedule_topmost()
        self.save()

    def toggle_theme(self):
        self.set_theme("dark" if self.settings.get("theme") == "light" else "light")

    def topmost_enabled(self):
        return bool(self.settings["mini_always_on_top"] if self.compact else self.settings["always_on_top"])

    def apply_topmost(self):
        """Keep floating Tk window above ordinary desktop app windows on Windows/macOS/Linux.

        Windows SetWindowPos complements Tk's -topmost, without stealing input focus.
        Exclusive fullscreen apps and system secure desktops are OS-controlled exceptions.
        """
        try:
            enabled=self.topmost_enabled()
            self.root.attributes("-topmost",enabled)
            if sys.platform=="win32":
                from ctypes import wintypes
                user32 = ctypes.windll.user32
                user32.GetAncestor.argtypes = [wintypes.HWND, wintypes.UINT]
                user32.GetAncestor.restype = wintypes.HWND
                user32.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND,
                                                  ctypes.c_int, ctypes.c_int,
                                                  ctypes.c_int, ctypes.c_int, wintypes.UINT]
                user32.SetWindowPos.restype = wintypes.BOOL
                native = int(self.root.winfo_id())
                hwnd = user32.GetAncestor(native, 2) or native  # GA_ROOT
                flag = 0x0002 | 0x0001 | 0x0010  # NO MOVE/SIZE/ACTIVATE
                user32.SetWindowPos(hwnd, ctypes.c_void_p(-1 if enabled else -2),
                                    0, 0, 0, 0, flag)
        except (tk.TclError,AttributeError,OSError,ValueError):
            pass

    def _schedule_topmost(self):
        self._cancel_after("_topmost_after")
        if not self._closing:
            self._topmost_after = self.root.after(150, self._reapply_topmost)

    def _reapply_topmost(self):
        self._topmost_after = None
        if not self._closing:self.apply_topmost()

    def apply_sleep_policy(self, release=False):
        """Prevent Windows idle *system* sleep, not monitor sleep or lock.

        Manual sleep, shutdown and forced termination remain under OS control.
        The request is owned by this process and released during explicit exit.
        """
        if sys.platform != "win32":return
        requested = bool(self.settings.get("prevent_sleep")) and not release
        if requested == self._sleep_active:return
        try:
            set_state = ctypes.windll.kernel32.SetThreadExecutionState
            set_state.argtypes = [ctypes.c_uint32]
            set_state.restype = ctypes.c_uint32
            flags = 0x80000000 | (0x00000001 if requested else 0)
            if not set_state(flags):
                LOGGER.warning("Windows rejected idle sleep request (enabled=%s)", requested)
                return
            self._sleep_active = requested
        except (AttributeError, OSError):
            LOGGER.exception("Unable to apply Windows sleep policy")

    def toggle_pin(self):
        self.settings["mini_always_on_top"]=not self.settings["mini_always_on_top"]
        self.apply_topmost()
        self.save()
        self.refresh()

    def toggle_mini(self):
        if not self.compact:
            self.full_geometry=self.root.geometry()
            self.compact=True
            self.page="focus"
            self.root.withdraw()
            self.build()
            self.root.deiconify()
        else:
            self.remember_mini_position()
            self.compact=False
            self.root.withdraw()
            self.build()
            self.root.geometry(self.full_geometry)
            self.root.deiconify()
        self._schedule_topmost()

    def start_drag(self,event):
        self.drag_start=(event.x_root-self.root.winfo_x(),event.y_root-self.root.winfo_y())

    def drag(self,event):
        if self.drag_start is None:return
        x=event.x_root-self.drag_start[0]
        y=event.y_root-self.drag_start[1]
        x=max(0,min(x,self.root.winfo_screenwidth()-self.root.winfo_width()))
        y=max(0,min(y,self.root.winfo_screenheight()-self.root.winfo_height()))
        self.root.geometry(f"+{x}+{y}")

    def remember_mini_position(self):
        self.state.setdefault("window",{})["mini_x"]=self.root.winfo_x()
        self.state["window"]["mini_y"]=self.root.winfo_y()
        self.save()

    def end_drag(self,_event=None):
        if self.drag_start is not None:self.remember_mini_position()
        self.drag_start=None

    def quick_add(self,_event=None):
        if self.compact:self.toggle_mini()
        if self.page!="focus":self.switch_page("focus")
        if self.entry:self.entry.focus_set();self.entry_focus()
        return "break"

    def spacebar(self,event):
        if event.widget.winfo_toplevel()!=self.root:return None
        if isinstance(event.widget,(tk.Entry,tk.Text,tk.Spinbox,Pill)):return None
        self.toggle_timer()
        return "break"

    def capture(self,path):
        try:
            from PIL import ImageGrab
            self.root.update()
            x,y=self.root.winfo_rootx(),self.root.winfo_rooty()
            width,height=self.root.winfo_width(),self.root.winfo_height()
            ImageGrab.grab(bbox=(x,y,x+width,y+height)).save(path)
        except Exception as e:
            print("Preview capture failed:",e,file=sys.stderr)
        finally:
            # Explicit development-only --screenshot no longer terminates the app.
            # Normal user sessions have no timed shutdown path.
            LOGGER.info("Preview capture finished")

    def close(self, _event=None):
        if self._closing:return "break"
        if not messagebox.askyesno("Tomato Focus 종료",
                "프로그램을 완전히 종료할까요?\n종료하면 회의 알림과 타이머가 중단됩니다.",
                parent=self.root, default="no"):
            return "break"
        self.shutdown()
        return "break"

    def shutdown(self):
        """Explicit exit only; save once and release callbacks and power request."""
        if self._closing:return
        self._closing = True
        for attr in ("_tick_after", "_meeting_after", "_topmost_after"):
            self._cancel_after(attr)
        try:
            if self.compact:
                self.state.setdefault("window", {})["mini_x"] = self.root.winfo_x()
                self.state["window"]["mini_y"] = self.root.winfo_y()
            self.record_partial()
            self.save()
            LOGGER.info("Explicit shutdown")
        finally:
            self.apply_sleep_policy(release=True)
            self.root.destroy()


def main():
    parser=argparse.ArgumentParser(description="Tomato Focus Tkinter desktop widget")
    parser.add_argument("--demo",action="store_true",help="Show demo content without saving")
    parser.add_argument("--screenshot",default=None,help=argparse.SUPPRESS)
    parser.add_argument("--mini",action="store_true",help="Launch straight into floating widget")
    args=parser.parse_args()
    configure_logging()
    try:
        root=tk.Tk()
        app=TomatoFocus(root,demo=args.demo,screenshot=args.screenshot)
        if args.mini:root.after(120,app.toggle_mini)
        root.mainloop()
        if not app._closing:
            LOGGER.warning("Main loop returned without explicit shutdown")
    except Exception:
        LOGGER.exception("Fatal application error")
        raise


if __name__=="__main__":
    main()
