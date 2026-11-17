# -*- coding: utf-8 -*-
"""Tomato Focus — Tkinter Pomodoro, To-do and week/month/year focus dashboard.

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
import math
from pathlib import Path
import random
import sys
import time
import tkinter as tk
from tkinter import font as tkfont, messagebox
import uuid

APP_NAME = "Tomato Focus"
DATA_PATH = Path.home() / ".focus_studio" / "state.json"

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
    "theme": "light",          # "light" / "dark", persisted across launches
}
MODE_TITLE = {"focus": "몰입 시간", "short": "짧은 휴식", "long": "긴 휴식"}
MODE_TAG = {"focus": "FOCUS", "short": "SHORT BREAK", "long": "LONG BREAK"}
DAY_KO = ["월", "화", "수", "목", "금", "토", "일"]


def font_family(root):
    families = set(tkfont.families(root))
    for f in ("Pretendard", "맑은 고딕", "Malgun Gothic", "Apple SD Gothic Neo",
              "Noto Sans CJK KR", "Segoe UI", "DejaVu Sans"):
        if f in families:
            return f
    return "TkDefaultFont"


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
        if text is not None:
            self.text = text
        if fill is not None:
            new_fill = P.get(fill, fill)
            if self.hover == self.fill:
                self.hover = new_fill
            self.fill = new_fill
        if fg is not None:
            self.fg = P.get(fg, fg)
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
        self.state = self.load()
        if demo:
            self.add_demo_content()
        self.settings = self.state["settings"]
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
        self.focus_cycle = sum(1 for s in self.state["sessions"] if s.get("date") == date.today().isoformat() and s.get("mode", "focus") == "focus") % self.settings["long_every"]
        self.filter_name = "all"
        self.summary_value = {}
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
        self.full_geometry = "1100x835"
        self.root.title(APP_NAME)
        self.root.configure(bg=P["bg"])
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.bind("<space>", self.spacebar)
        self.root.bind("<Control-n>", self.quick_add)
        self.root.bind("<Control-m>", lambda e: self.toggle_mini())
        self.root.bind("<Escape>", lambda e: self.toggle_mini() if self.compact else None)
        self.root.geometry(self.full_geometry)
        self.root.minsize(900, 720)
        self.root.resizable(True, True)
        self.build()
        self.root.after(200, self.tick)
        self.apply_topmost()
        if screenshot:
            # Only used for optional development previews. Pillow is not needed to run the app.
            self.root.after(850, lambda: self.capture(screenshot))

    @staticmethod
    def fresh_state():
        return {"tasks": [], "sessions": [], "settings": dict(DEFAULT_SETTINGS),
                "active_task": None, "window": {}}

    def load(self):
        state = self.fresh_state()
        try:
            existing = json.loads(DATA_PATH.read_text(encoding="utf-8"))
            if not isinstance(existing, dict):
                return state
            state["tasks"] = [x for x in existing.get("tasks", []) if isinstance(x, dict)] if isinstance(existing.get("tasks", []), list) else []
            state["sessions"] = [x for x in existing.get("sessions", []) if isinstance(x, dict)] if isinstance(existing.get("sessions", []), list) else []
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
            temp.write_text(json.dumps(self.state, ensure_ascii=False, indent=2), encoding="utf-8")
            temp.replace(DATA_PATH)
        except OSError as e:
            self.status = f"저장하지 못했습니다: {e}"

    def label(self, parent, text, *, size=11, color="text", weight="normal", bg=None, **kw):
        return tk.Label(parent, text=text, bg=bg or parent.cget("bg"), fg=P.get(color, color),
                        font=(self.font_name,size,weight), **kw)

    def btn(self, parent, text, command, *, width=115, height=38, fill="white", fg="text",
            border=None, hover=None, radius=14, size=10):
        return Pill(parent,text,command,width=width,height=height,fill=fill,fg=fg,
                    border=border,hover=hover,radius=radius,fontsize=size)

    def clear_widgets(self):
        for child in self.root.winfo_children():
            child.destroy()
        self.summary_value = {}
        self.timer_label = self.primary_button = self.status_label = self.cycle_canvas = None
        self.scene = self.task_area = self.entry = self.task_scroll = None
        self.nav_buttons, self.mode_buttons, self.period_buttons = {}, {}, {}
        self.chart_canvas = self.heat_canvas = self.period_caption = self.stats_info = None
        self.stats_summary = {}
        self.mini_pin = self.mini_task_label = None

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
        self.btn(right,"⚙ 설정",self.settings_dialog,width=94,height=37,fill="white",border="line").pack(side="right",padx=(8,0))
        self.btn(right,"☾ 다크" if self.settings["theme"] == "light" else "☀ 라이트",
                 self.toggle_theme,width=94,height=37,fill="surface",fg="text",border="line").pack(side="right",padx=(8,0))
        self.btn(right,"▣ 미니 위젯",self.toggle_mini,width=121,height=37,fill="red",fg="on_accent",hover="red_dark").pack(side="right",padx=(8,0))
        for pg,name in (("focus","집중 · 할 일"),("stats","몰입 통계")):
            b = self.btn(right,name,lambda p=pg:self.switch_page(p),width=119,height=37,
                         fill="red_pale" if pg==self.page else "white",
                         fg="red" if pg==self.page else "muted",
                         border=None if pg==self.page else "line")
            b.pack(side="left",padx=(0,7))
            self.nav_buttons[pg]=b
        if self.page=="focus":
            self.build_dashboard(shell)
        else:
            self.build_statistics(shell)
        foot=tk.Frame(shell,bg=P["bg"])
        foot.pack(fill="x",pady=(10,0))
        self.status_label=self.label(foot,"",size=9,color="muted")
        self.status_label.pack(side="left")
        self.label(foot,"SPACE 시작/멈춤  ·  CTRL+N 할 일  ·  CTRL+M 미니 위젯",
                   size=9,color="hint").pack(side="right")

    def build_dashboard(self, shell):
        top=tk.Frame(shell,bg=P["bg"])
        top.pack(fill="x",pady=(0,15))
        dt=datetime.now()
        self.label(top,"오늘도, 토마토 한 알만큼 집중해요.",size=19,weight="bold").pack(anchor="w")
        self.label(top,f"{dt:%Y.%m.%d}  ·  작고 꾸준한 몰입의 기록",size=10,color="muted").pack(anchor="w",pady=(3,0))
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
        y=max(0,min(y,max(0,self.root.winfo_screenheight()-435)))
        self.root.geometry(f"320x430+{x}+{y}")
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

    def add_task(self):
        if not self.entry:return
        title=self.entry.get().strip()
        if not title or title=="할 일을 입력해 주세요": return
        if len(title)>180:
            messagebox.showwarning("할 일 추가","할 일은 180자 이하로 입력해 주세요.",parent=self.root)
            return
        self.state["tasks"].insert(0,{"id":uuid.uuid4().hex[:12],"title":title,"done":False,
                                       "priority":False,"created_at":date.today().isoformat(),
                                       "completed_on":None})
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
        t["done"]=not t.get("done",False)
        t["completed_on"]=date.today().isoformat() if t["done"] else None
        if t["done"] and self.active_task==task_id:self.active_task=None
        self.save();self.refresh()

    def priority_task(self,task_id):
        t=self.get_task(task_id)
        if t:t["priority"]=not t.get("priority",False);self.save();self.render_tasks()

    def choose_task(self,task_id):
        t=self.get_task(task_id)
        if t and not t.get("done"):
            self.active_task = None if self.active_task==task_id else task_id
            self.save();self.refresh()

    def delete_task(self,task_id):
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
        for child in self.task_area.winfo_children():child.destroy()
        for key,button in self.task_filter_buttons.items():
            on=key==self.filter_name
            button.set(fill="red_pale" if on else "white",fg="red" if on else "muted")
        items=sorted(self.state["tasks"],key=lambda t:(bool(t.get("done")),not bool(t.get("priority"))))
        if self.filter_name=="active":items=[x for x in items if not x.get("done")]
        if self.filter_name=="done":items=[x for x in items if x.get("done")]
        self.task_count.configure(text=f"{sum(not x.get('done') for x in self.state['tasks'])}개 진행 중")
        if not items:
            self.label(self.task_area,"할 일이 없어요. 첫 번째 토마토를 심어볼까요?",size=10,color="muted").pack(pady=35)
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
            text=self.label(r,t.get("title","제목 없음"),size=10,color="hint" if done else "text",
                            bg=bg,anchor="w",cursor="hand2")
            text.pack(side="left",fill="x",expand=True,padx=(3,1))
            if done:
                f=tkfont.Font(family=self.font_name,size=10,overstrike=True)
                text.config(font=f);text._preserved_font=f
            text.bind("<Button-1>",lambda e,i=tid:self.choose_task(i))
            self.btn(r,"★" if t.get("priority") else "☆",lambda i=tid:self.priority_task(i),
                     width=30,height=31,fill=bg,fg="orange" if t.get("priority") else "hint",size=12).pack(side="right")
            self.btn(r,"×",lambda i=tid:self.delete_task(i),width=27,height=31,
                     fill=bg,fg="hint",size=13).pack(side="right")
            for widget in (r,*r.winfo_children()):
                widget.bind("<MouseWheel>",self.mouse_scroll)
        self.task_area.update_idletasks()
        self.task_scroll.configure(scrollregion=self.task_scroll.bbox("all"))

    def active_task_title(self):
        obj=self.get_task(self.active_task)
        return str(obj.get("title","")) if obj else ""

    @staticmethod
    def mins(value):
        try:
            return max(0,int(value))
        except (ValueError,TypeError):
            return 0

    def date_totals(self):
        totals={}
        for s in self.state["sessions"]:
            key=s.get("date")
            try:
                date.fromisoformat(key)
            except (ValueError,TypeError):
                continue
            totals[key]=totals.get(key,0)+self.mins(s.get("minutes",0))
        return totals

    def today_totals(self):
        today=date.today().isoformat()
        sessions=[s for s in self.state["sessions"] if s.get("date")==today]
        return sum(self.mins(s.get("minutes",0)) for s in sessions),len(sessions)

    def refresh(self):
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
            self.focus_started_at=datetime.now().isoformat(timespec="seconds")
        self.running=True
        self.deadline=time.monotonic()+self.remaining
        self.status="집중 중! 지금 하는 일 하나에만 마음을 모아요."
        self.refresh()

    def pause_timer(self):
        if not self.running:return
        self.remaining=max(0,math.ceil(self.deadline-time.monotonic()))
        self.running=False
        self.deadline=None
        self.pause_since=time.monotonic()
        if self.mode=="focus":self.pause_count+=1
        self.status="잠시 멈췄어요. 다시 이어서 할 수 있어요."
        self.refresh()

    def reset_session_meta(self):
        self.pause_count=0
        self.pause_total=0
        self.pause_since=None
        self.focus_started_at=None
        self.session_started=False

    def reset_timer(self):
        self.running=False
        self.deadline=None
        self.remaining=60*self.settings[self.mode]
        self.reset_session_meta()
        self.status="타이머를 초기화했어요."
        self.refresh()

    def switch_mode(self,mode):
        if mode not in MODE_TITLE:return
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
        self.status="다음 단계로 넘어갔어요. 건너뛴 시간은 기록하지 않아요."
        self.refresh()

    def finish_session(self):
        old=self.mode
        self.running=False
        self.deadline=None
        if old=="focus":
            self.state["sessions"].append({
                "date":date.today().isoformat(),
                "minutes":self.settings["focus"],
                "mode":"focus",
                "task_id":self.active_task,
                "task_title":self.active_task_title(),
                "started_at":self.focus_started_at,
                "finished_at":datetime.now().isoformat(timespec="seconds"),
                "pause_count":self.pause_count,
                "pause_seconds":round(self.pause_total),
            })
            self.focus_cycle+=1
            if self.focus_cycle>=self.settings["long_every"]:
                self.focus_cycle=0
                self.mode="long"
            else:self.mode="short"
            self.status="토마토 수확 완료! 휴식할 시간이 왔어요."
        else:
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

    def tick(self):
        try:
            if self.running and self.deadline is not None:
                new=max(0,math.ceil(self.deadline-time.monotonic()))
                if new!=self.remaining:
                    self.remaining=new
                    if self.timer_label is not None:
                        self.timer_label.config(text=f"{new//60:02d}:{new%60:02d}")
                if self.remaining==0:
                    self.finish_session()
            self.root.after(200,self.tick)
        except tk.TclError:
            pass

    def switch_page(self,page):
        if self.compact or page==self.page:return
        self.page=page
        self.build()

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
        days=self.period_days()
        totals=self.date_totals()
        vals=[totals.get(d.isoformat(),0) for d in days]
        keyset={d.isoformat() for d in days}
        sessions=[s for s in self.state["sessions"] if s.get("date") in keyset]
        uninterrupt=[s for s in sessions if type(s.get("pause_count")) is int]
        clean=round(sum(s["pause_count"]==0 for s in uninterrupt)*100/len(uninterrupt)) if uninterrupt else None
        return days,vals,sessions,clean,totals

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
        days,vals,sessions,clean,_=self.stats_data()
        overview={"total":sum(vals),"count":len(sessions),"days":sum(x>0 for x in vals),
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
        dlg.geometry("435x650")
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
        for name,var in (("미니 위젯을 다른 창보다 항상 위에 표시",mini_pin),
                         ("메인 대시보드도 항상 위에 표시",main_pin),
                         ("집중 완료 후 휴식 자동 시작",auto)):
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
            self.root.after_idle(self.apply_topmost)
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
        self.root.after(70,self.apply_topmost)
        self.root.after(220,self.apply_topmost)

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
            self.close()

    def close(self):
        if self.compact:self.remember_mini_position()
        self.save()
        self.root.destroy()


def main():
    parser=argparse.ArgumentParser(description="Tomato Focus Tkinter desktop widget")
    parser.add_argument("--demo",action="store_true",help="Show demo content without saving")
    parser.add_argument("--screenshot",default=None,help=argparse.SUPPRESS)
    parser.add_argument("--mini",action="store_true",help="Launch straight into floating widget")
    args=parser.parse_args()
    root=tk.Tk()
    app=TomatoFocus(root,demo=args.demo,screenshot=args.screenshot)
    if args.mini:root.after(120,app.toggle_mini)
    root.mainloop()


if __name__=="__main__":
    main()
