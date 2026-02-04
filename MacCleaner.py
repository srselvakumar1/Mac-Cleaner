import tkinter as tk
from tkinter import ttk, messagebox, filedialog, PhotoImage
import os
import shutil
import threading
import time
from datetime import datetime
import re
import json
from pathlib import Path
import subprocess
import logging
from typing import Dict, List, Tuple, Optional
from concurrent.futures import ThreadPoolExecutor, as_completed

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Configuration Constants
MAX_SCAN_DEPTH = 2
UI_UPDATE_BATCH_SIZE = 10
CLEANING_UPDATE_BATCH_SIZE = 5
MIN_FILE_SIZE_BYTES = 0  # Minimum file size to consider (0 = all files)
TREE_DISPLAY_LIMIT = 1000  # Maximum items to display in tree
MAX_DELETION_WORKERS = 8  # Number of parallel deletion threads

class MacCleanerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        
        # App configuration
        self.title("iMac Cleaner Pro")
        self.geometry("1050x800")
        self.resizable(False, False)  # Make non-resizable
        
        # Modern color scheme (macOS Big Sur inspired)
        self.colors = {
            "primary": "#007AFF",
            "primary_hover": "#0051D5",
            "secondary": "#34C759",
            "warning": "#FF9500",
            "danger": "#FF3B30",
            "background": "#FFFFFF",
            "surface": "#F5F5F7",
            "surface_elevated": "#FAFAFA",
            "dark": "#1D1D1F",
            "text_primary": "#1D1D1F",
            "text_secondary": "#86868B",
            "border": "#D2D2D7",
            "shadow": "#00000015"
        }
        
        # Configure window background
        self.configure(bg=self.colors["background"])
        
        # Fonts
        self.fonts = {
            "title": ("SF Pro Display", 30, "bold"),
            "subtitle": ("SF Pro Display", 16, "bold"),
            "body": ("SF Pro Text", 12),
            "small": ("SF Pro Text", 10),
            "button": ("SF Pro Text", 12, "bold")
        }

        # Set app icon if available
        try:
            self.iconphoto(True, tk.PhotoImage(file="wheel.png"))
        except:
            pass
        
        # App variables
        self.scanning = False
        self.cleaning = False
        self.selected_items = {}
        self.total_files = 0
        self.total_size = 0
        self.cleaned_files = 0
        self.cleaned_size = 0
        self.size_cache: Dict[str, int] = {}  # Cache for formatted sizes
        self.tree_item_count = 0  # Track tree items to prevent overflow
        self.file_categories = {
        # System Caches (Safe)
        "cache": {"title": "Application Cache", "path": "~/Library/Caches", "selected": True, "color": "#007AFF"},
        "logs": {"title": "User App Logs", "path": "~/Library/Logs", "selected": True, "color": "#5856D6"},
        
        # Temporary Files (Safe)
        "temp": {"title": "User Temp Files", "path": "/tmp", "selected": True, "color": "#FF9500"},
        "var_tmp": {"title": "System Temp Files", "path": "/private/var/tmp", "selected": True, "color": "#FF9F0A"},
        
        # Browser Caches (Safe)
        "safari_cache": {"title": "Safari Cache", "path": "~/Library/Caches/com.apple.Safari", "selected": False, "color": "#34C759"},
        "chrome_cache": {"title": "Chrome Cache", "path": "~/Library/Caches/Google/Chrome", "selected": False, "color": "#AF52DE"},
        "firefox_cache": {"title": "Firefox Cache", "path": "~/Library/Caches/Firefox", "selected": True, "color": "#FF6482"},
        "edge_cache": {"title": "Edge Cache", "path": "~/Library/Caches/Microsoft Edge", "selected": True, "color": "#0078D4"},
        
        # Mail & Messages Cache (Safe)
        "mail_cache": {"title": "Mail Cache", "path": "~/Library/Caches/com.apple.mail", "selected": True, "color": "#0071E3"},
        "messages_cache": {"title": "Messages Cache", "path": "~/Library/Messages/Cache", "selected": True, "color": "#30D158"},
        
        # Development Tools (Safe - will regenerate)
        "xcode_cache": {"title": "Xcode Derived Data", "path": "~/Library/Developer/Xcode/DerivedData", "selected": False, "color": "#007AFF"},
        "cocoapods_cache": {"title": "CocoaPods Cache", "path": "~/Library/Caches/CocoaPods", "selected": False, "color": "#EE3124"},
        "npm_cache": {"title": "NPM Cache", "path": "~/.npm", "selected": False, "color": "#CB3837"},
        "yarn_cache": {"title": "Yarn Cache", "path": "~/Library/Caches/Yarn", "selected": False, "color": "#2C8EBB"},
        "pip_cache": {"title": "Python Pip Cache", "path": "~/Library/Caches/pip", "selected": False, "color": "#3776AB"},
        
        # iOS Logs (Safe)
        "ios_logs": {"title": "iOS Device Logs", "path": "~/Library/Logs/CrashReporter/MobileDevice", "selected": True, "color": "#FF6482"},
        
        # Trash (Safe)
        "trash": {"title": "Trash Contents", "path": "~/.Trash", "selected": True, "color": "#FF3B30"},
        
        # Font & System Caches (Safe - will regenerate)
        "font_cache": {"title": "Font Cache", "path": "~/Library/Caches/com.apple.FontRegistry", "selected": True, "color": "#BF5AF2"},
        "quicklook_cache": {"title": "QuickLook Cache", "path": "~/Library/Caches/com.apple.QuickLookDaemon", "selected": True, "color": "#64D2FF"},
    }
        
        # Setup UI
        self.setup_ui()
        self.create_menu()
        
        # Bindings
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        
    def setup_ui(self):
        # Main frame with reduced padding
        main_frame = tk.Frame(self, bg=self.colors["background"])
        main_frame.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        # Modern style configuration
        style = ttk.Style()
        style.theme_use('clam')  # Better theme for customization
        
        # Configure styles
        style.configure("TFrame", background=self.colors["background"])
        style.configure("Card.TFrame", background=self.colors["surface_elevated"], 
                       relief=tk.FLAT, borderwidth=0)
        
        style.configure("TLabel", background=self.colors["background"], 
                       font=self.fonts["body"], foreground=self.colors["text_primary"])
        style.configure("Title.TLabel", font=self.fonts["title"], 
                       foreground=self.colors["text_primary"])
        style.configure("Subtitle.TLabel", font=self.fonts["subtitle"],
                       foreground=self.colors["text_primary"])
        style.configure("Small.TLabel", font=self.fonts["small"], 
                       foreground=self.colors["text_secondary"])
        
        # Modern button styles
        style.configure("Primary.TButton", font=self.fonts["button"], 
                       background=self.colors["primary"], foreground="white",
                       borderwidth=0, focuscolor='none', padding=(20, 10))
        style.map("Primary.TButton",
                 background=[("active", self.colors["primary_hover"]), 
                           ("pressed", self.colors["primary_hover"])])
        
        style.configure("Secondary.TButton", font=self.fonts["button"],
                       background=self.colors["secondary"], foreground="white",
                       borderwidth=0, focuscolor='none', padding=(20, 10))
        
        style.configure("Danger.TButton", font=self.fonts["button"],
                       background=self.colors["danger"], foreground="white",
                       borderwidth=0, focuscolor='none', padding=(20, 10))
        
        style.configure("TCheckbutton", background=self.colors["surface_elevated"], 
                       font=self.fonts["body"], foreground=self.colors["text_primary"])
        style.configure("TProgressbar", background=self.colors["primary"], 
                       troughcolor=self.colors["surface"], borderwidth=0,
                       thickness=8)
        
        # Header with gradient effect (colored background)
        header_frame = tk.Frame(main_frame, bg=self.colors["primary"], height=70)
        header_frame.pack(fill=tk.X, pady=(0, 15))
        header_frame.pack_propagate(False)
        
        # Title with icon placeholder
        title_container = tk.Frame(header_frame, bg=self.colors["primary"])
        title_container.pack(side=tk.LEFT, fill=tk.Y, pady=10, padx=15)
        
        title_label = tk.Label(title_container, text="🧹 iMac Cleaner Pro",
                              font=self.fonts["title"],
                              bg=self.colors["primary"],
                              fg="white")
        title_label.pack(side=tk.LEFT)
        
        # Status indicator
        status_container = tk.Frame(header_frame, bg=self.colors["primary"])
        status_container.pack(side=tk.RIGHT, fill=tk.Y, pady=10, padx=15)
        
        self.status_var = tk.StringVar(value="Ready to scan")
        self.status_label = tk.Label(status_container, textvariable=self.status_var,
                                     bg=self.colors["primary"],
                                     fg="white",
                                     font=self.fonts["small"],
                                     anchor=tk.E)
        self.status_label.pack(side=tk.RIGHT, padx=10)
        
        # Status dot indicator with dynamic color
        self.status_dot = tk.Canvas(status_container, width=10, height=10, 
                                   bg=self.colors["primary"], highlightthickness=0)
        self.status_dot.pack(side=tk.RIGHT, padx=(0, 5))
        self.status_dot_circle = self.status_dot.create_oval(1, 1, 9, 9, 
                                                             fill="white", 
                                                             outline="")
        
        # Main content frame with two columns
        content_frame = tk.Frame(main_frame, bg=self.colors["background"])
        content_frame.pack(fill=tk.BOTH, expand=True)
        
        # Left column - Categories (Card style)
        left_card = tk.Frame(content_frame, bg=self.colors["surface_elevated"],
                            relief=tk.FLAT, bd=0)
        left_card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 10))
        
        # Add subtle shadow effect with border
        left_inner = tk.Frame(left_card, bg=self.colors["surface_elevated"])
        left_inner.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        
        categories_header = tk.Frame(left_inner, bg=self.colors["surface_elevated"])
        categories_header.pack(fill=tk.X, padx=15, pady=(15, 8))
        
        categories_label = ttk.Label(categories_header, text="Cleaning Categories", 
                                     style="Subtitle.TLabel")
        categories_label.pack(side=tk.LEFT)
        
        # Category selection frame with scrollbar
        categories_canvas = tk.Canvas(left_inner, bg=self.colors["surface_elevated"], 
                                     highlightthickness=0)
        categories_scrollbar = ttk.Scrollbar(left_inner, orient="vertical", 
                                            command=categories_canvas.yview)
        categories_frame = tk.Frame(categories_canvas, bg=self.colors["surface_elevated"])
        
        categories_canvas.configure(yscrollcommand=categories_scrollbar.set)
        categories_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=15, pady=(0, 15))
        categories_scrollbar.pack(side=tk.RIGHT, fill=tk.Y, padx=(0, 8))
        
        categories_canvas.create_window((0, 0), window=categories_frame, anchor=tk.NW)
        categories_frame.bind("<Configure>", 
                             lambda e: categories_canvas.configure(scrollregion=categories_canvas.bbox("all")))
        
        # Add category checkboxes with modern styling
        self.category_vars = {}
        for key, data in self.file_categories.items():
            self.category_vars[key] = tk.BooleanVar(value=data["selected"])
            
            # Category item container with hover effect
            category_frame = tk.Frame(categories_frame, bg=self.colors["surface_elevated"])
            category_frame.pack(fill=tk.X, pady=4)
            
            # Color indicator (rounded)
            color_indicator = tk.Canvas(category_frame, width=4, height=24, 
                                       bg=self.colors["surface_elevated"], 
                                       highlightthickness=0)
            color_indicator.pack(side=tk.LEFT, padx=(0, 12))
            color_indicator.create_rectangle(0, 0, 4, 24, fill=data["color"], 
                                            outline="")
            
            checkbox = ttk.Checkbutton(category_frame, text=data["title"], 
                                      variable=self.category_vars[key])
            checkbox.pack(side=tk.LEFT, fill=tk.X, expand=True)
            
            size_var = tk.StringVar(value="--")
            size_label = tk.Label(category_frame, textvariable=size_var, width=10,
                                 bg=self.colors["surface_elevated"],
                                 fg=self.colors["text_secondary"],
                                 font=self.fonts["small"])
            size_label.pack(side=tk.RIGHT, padx=(10, 0))
            
            self.file_categories[key]["size_var"] = size_var
        
        # Right column - File list and details (Card style)
        right_card = tk.Frame(content_frame, bg=self.colors["surface_elevated"],
                             relief=tk.FLAT, bd=0)
        right_card.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(10, 0))
        
        right_inner = tk.Frame(right_card, bg=self.colors["surface_elevated"])
        right_inner.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        
        # Files preview header
        preview_header = tk.Frame(right_inner, bg=self.colors["surface_elevated"])
        preview_header.pack(fill=tk.X, padx=15, pady=(15, 8))
        
        preview_label = ttk.Label(preview_header, text="Files Preview", 
                                 style="Subtitle.TLabel")
        preview_label.pack(side=tk.LEFT)
        
        # Add file count indicator
        self.preview_count_var = tk.StringVar(value="")
        self.preview_count_label = tk.Label(preview_header, 
                                           textvariable=self.preview_count_var,
                                           bg=self.colors["surface_elevated"],
                                           fg=self.colors["text_secondary"],
                                           font=self.fonts["small"])
        self.preview_count_label.pack(side=tk.RIGHT)
        
        # File tree view with modern styling
        tree_container = tk.Frame(right_inner, bg=self.colors["surface_elevated"])
        tree_container.pack(fill=tk.BOTH, expand=True, padx=15, pady=(0, 15))
        
        # Create tree with scrollbars (vertical only)
        self.tree = ttk.Treeview(tree_container, columns=("size", "date"), 
                                show="tree headings", height=15)
        vsb = ttk.Scrollbar(tree_container, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        
        # Modern tree styling with color-coded rows
        style.configure("Treeview", background=self.colors["background"],
                       foreground=self.colors["text_primary"],
                       fieldbackground=self.colors["background"],
                       borderwidth=0, font=self.fonts["body"],
                       rowheight=25)
        style.configure("Treeview.Heading", background=self.colors["surface"],
                       foreground=self.colors["primary"],  # Blue headers
                       borderwidth=0, font=self.fonts["button"],
                       relief=tk.FLAT)
        style.map("Treeview", 
                 background=[("selected", self.colors["primary"])],
                 foreground=[("selected", "white")])
        
        # Tree headings with better labels
        self.tree.heading("#0", text="📁 File/Folder", anchor=tk.W)
        self.tree.heading("size", text="💾 Size", anchor=tk.E)
        self.tree.heading("date", text="📅 Modified", anchor=tk.W)
        
        # Enhanced tree column widths - all columns visible and properly sized
        self.tree.column("#0", width=280, minwidth=200, stretch=True)
        self.tree.column("size", width=140, minwidth=120, stretch=False, anchor=tk.E)
        self.tree.column("date", width=180, minwidth=150, stretch=False, anchor=tk.W)
        
        # Pack scrollbars first, then tree (correct order for alignment)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        
        # Summary frame with modern card design
        summary_card = tk.Frame(main_frame, bg=self.colors["surface_elevated"],
                               relief=tk.FLAT, bd=0)
        summary_card.pack(fill=tk.X, pady=15)
        
        summary_inner = tk.Frame(summary_card, bg=self.colors["surface_elevated"])
        summary_inner.pack(fill=tk.X, padx=2, pady=2)
        
        # Left side of summary - stats with icons
        stats_frame = tk.Frame(summary_inner, bg=self.colors["surface_elevated"])
        stats_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=15, pady=12)
        
        self.files_count_var = tk.StringVar(value="📄 Files: 0")
        files_count_label = tk.Label(stats_frame, textvariable=self.files_count_var,
                                    bg=self.colors["surface_elevated"],
                                    fg=self.colors["primary"],  # Blue
                                    font=(self.fonts["body"][0], self.fonts["body"][1], "bold"))
        files_count_label.pack(side=tk.LEFT, padx=10)
        
        self.total_size_var = tk.StringVar(value="💾 Size: 0 MB")
        total_size_label = tk.Label(stats_frame, textvariable=self.total_size_var,
                                   bg=self.colors["surface_elevated"],
                                   fg=self.colors["secondary"],  # Green
                                   font=(self.fonts["body"][0], self.fonts["body"][1], "bold"))
        total_size_label.pack(side=tk.LEFT, padx=10)
        
        # Right side of summary - modern action buttons
        buttons_frame = tk.Frame(summary_inner, bg=self.colors["surface_elevated"])
        buttons_frame.pack(side=tk.RIGHT, padx=15, pady=12)
        
        self.scan_button = ttk.Button(buttons_frame, text="Scan Files", 
                                     command=self.start_scan, style="Primary.TButton")
        self.scan_button.pack(side=tk.LEFT, padx=5)
        
        self.clean_button = ttk.Button(buttons_frame, text="Clean Selected", 
                                      command=self.clean_selected, state=tk.DISABLED,
                                      style="Secondary.TButton")
        self.clean_button.pack(side=tk.LEFT, padx=5)
        
        self.clean_all_button = ttk.Button(buttons_frame, text="Clean All", 
                                          command=self.clean_all, state=tk.DISABLED,
                                          style="Secondary.TButton")
        self.clean_all_button.pack(side=tk.LEFT, padx=5)

        # Close button
        self.close_button = ttk.Button(buttons_frame, text="Close", 
                                      command=self.on_close, style="Danger.TButton")
        self.close_button.pack(side=tk.LEFT, padx=5)

        # Modern progress bar with rounded appearance
        progress_container = tk.Frame(main_frame, bg=self.colors["background"])
        progress_container.pack(fill=tk.X, pady=(0, 12))
        
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(progress_container, variable=self.progress_var, 
                                           maximum=100, mode='determinate')
        self.progress_bar.pack(fill=tk.X)
        
        # Modern status bar
        status_bar_frame = tk.Frame(main_frame, bg=self.colors["surface"], 
                                   relief=tk.FLAT, height=40)
        status_bar_frame.pack(fill=tk.X, side=tk.BOTTOM)
        status_bar_frame.pack_propagate(False)
        
        status_inner = tk.Frame(status_bar_frame, bg=self.colors["surface"])
        status_inner.pack(fill=tk.BOTH, expand=True, padx=15, pady=8)
        
        self.status_detail_var = tk.StringVar(value="Welcome to iMac Cleaner Pro")
        self.status_detail_label = tk.Label(status_inner, 
                                           textvariable=self.status_detail_var,
                                           bg=self.colors["surface"],
                                           fg=self.colors["text_primary"],  # Darker for better readability
                                           font=self.fonts["body"], 
                                           anchor=tk.W)
        self.status_detail_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        self.time_var = tk.StringVar()
        time_label = tk.Label(status_inner, textvariable=self.time_var,
                             bg=self.colors["surface"],
                             fg=self.colors["primary"],  # Blue for visibility
                             font=(self.fonts["body"][0], 14, "bold"))  # Larger and bold
        time_label.pack(side=tk.RIGHT, padx=10)
        
        # Update time
        self.update_time()
    
    def update_status_color(self, state: str):
        """Update status dot color based on state (text stays white on blue background)."""
        color_map = {
            "ready": "#90EE90",        # Light green
            "scanning": "#FFD700",     # Gold/Yellow
            "cleaning": "#FFA500",     # Orange
            "complete": "#90EE90",     # Light green
            "error": "#FF6B6B"         # Light red
        }
        
        color = color_map.get(state, "white")
        # Only update dot color, text stays white
        self.status_dot.itemconfig(self.status_dot_circle, fill=color)
    
    def create_menu(self):
        menubar = tk.Menu(self)
        self.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Scan", command=self.start_scan)
        file_menu.add_command(label="Clean Selected", command=self.clean_selected)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_close)
        
        # Edit menu
        edit_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Edit", menu=edit_menu)
        edit_menu.add_command(label="Select All", command=self.select_all_categories)
        edit_menu.add_command(label="Deselect All", command=self.deselect_all_categories)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="About", command=self.show_about)
        help_menu.add_command(label="User Guide", command=self.show_help)
    
    def update_time(self):
        current_time = datetime.now().strftime("%H:%M:%S")
        self.time_var.set(f"🕐 {current_time}")
        self.after(1000, self.update_time)
    
    def start_scan(self):
        # Reset previous data
        self.tree.delete(*self.tree.get_children())
        self.total_files = 0
        self.total_size = 0
        self.tree_item_count = 0  # Reset tree item counter
        self.size_cache.clear()  # Clear size cache
        
        # Update UI for scanning state
        self.status_var.set("Scanning...")
        self.update_status_color("scanning")
        self.scan_button.configure(state=tk.DISABLED)
        self.clean_button.configure(state=tk.DISABLED)
        self.clean_all_button.configure(state=tk.DISABLED)
        self.close_button.configure(state=tk.DISABLED)
        self.progress_var.set(0)
        self.scanning = True
        
        # Start scanning thread
        scan_thread = threading.Thread(target=self.scan_system)
        scan_thread.daemon = True
        scan_thread.start()
    
    def scan_system(self):
        try:
            self.status_detail_var.set("Initializing scan...")
            time.sleep(0.5)  # Give UI time to update
            
            # Clear previous data
            for key in self.file_categories:
                self.file_categories[key]["size_var"].set("--")
                self.file_categories[key]["files"] = []
                self.file_categories[key]["total_size"] = 0
            
            # Scan each selected category
            categories_to_scan = [k for k, v in self.category_vars.items() if v.get()]
            total_categories = len(categories_to_scan)
            
            for i, category in enumerate(categories_to_scan):
                cat_data = self.file_categories[category]
                
                # Calculate progress for this category
                category_start_progress = (i / total_categories) * 100
                category_end_progress = ((i + 1) / total_categories) * 100
                self.current_category_progress = (category_start_progress, category_end_progress)
                
                # Update status
                self.status_detail_var.set(f"Scanning {cat_data['title']}...")
                self.progress_var.set(category_start_progress)
                
                # Expand path
                path = os.path.expanduser(cat_data["path"])
                
                # Scan if path exists
                if os.path.exists(path):
                    # Create parent node in tree
                    parent_id = self.tree.insert("", "end", text=cat_data["title"], 
                                               values=("", ""), open=True)
                    
                    # Scan directory
                    self.scan_directory(path, parent_id, category)
                    
                    # Update category size
                    size_str = self.format_size(cat_data["total_size"])
                    cat_data["size_var"].set(size_str)
                    
                    # Update preview count
                    if self.tree_item_count >= TREE_DISPLAY_LIMIT:
                        self.preview_count_var.set(f"Showing {TREE_DISPLAY_LIMIT}+ items")
                    else:
                        self.preview_count_var.set(f"{self.tree_item_count} items")
                
                # Update progress to end of category
                self.progress_var.set(category_end_progress)
            
            # Scanning complete
            self.scanning = False
            self.progress_var.set(100)
            self.status_var.set("Scan complete")
            self.update_status_color("complete")
            self.status_detail_var.set(f"Found {self.total_files} files ({self.format_size(self.total_size)})")
            self.files_count_var.set(f"Files: {self.total_files}")
            self.total_size_var.set(f"Size: {self.format_size(self.total_size)}")
            
            # Enable buttons based on results
            self.scan_button.configure(state=tk.NORMAL)
            if self.total_files > 0:
                self.clean_button.configure(state=tk.NORMAL)
                self.clean_all_button.configure(state=tk.NORMAL)
                self.close_button.configure(state=tk.NORMAL)
            
        except Exception as e:
            self.status_var.set("Scan error")
            self.update_status_color("error")
            self.status_detail_var.set(f"Error: {str(e)}")
            self.scanning = False
            self.scan_button.configure(state=tk.NORMAL)
    
    def scan_directory(self, path: str, parent_id: str, category: str, 
                      max_depth: int = MAX_SCAN_DEPTH, current_depth: int = 0) -> None:
        """Optimized directory scanning using os.scandir() for better performance."""
        try:
            if current_depth > max_depth:
                # Count files without displaying for deep directories
                stats = self._count_deep_files(path, category)
                if stats['count'] > 0 and self.tree_item_count < TREE_DISPLAY_LIMIT:
                    self.tree.insert(parent_id, "end", 
                                   text=f"{stats['count']} files in subdirectories",
                                   values=(self.format_size(stats['size']), ""))
                    self.tree_item_count += 1
                return
            
            # Use scandir for better performance
            try:
                with os.scandir(path) as entries:
                    for entry in entries:
                        if not self.scanning:
                            break
                        
                        try:
                            # Skip certain system files
                            if entry.name.startswith(".") and entry.name not in [".Trash", ".DS_Store"]:
                                continue
                            
                            # Get stats efficiently
                            stat_info = entry.stat(follow_symlinks=False)
                            size = stat_info.st_size
                            
                            # Skip files below minimum size threshold
                            if not entry.is_dir() and size < MIN_FILE_SIZE_BYTES:
                                continue
                            
                            mod_time = datetime.fromtimestamp(stat_info.st_mtime).strftime("%Y-%m-%d %H:%M")
                            
                            if entry.is_dir(follow_symlinks=False):
                                # Directory - only add to tree if under display limit
                                if self.tree_item_count < TREE_DISPLAY_LIMIT:
                                    dir_id = self.tree.insert(parent_id, "end", text=entry.name,
                                                           values=("Directory", mod_time))
                                    self.tree_item_count += 1
                                else:
                                    dir_id = parent_id  # Don't create new tree item
                                
                                # Recursively scan subdirectory
                                self.scan_directory(entry.path, dir_id, category, 
                                                  max_depth, current_depth + 1)
                            else:
                                # File - add to tree if under display limit
                                if self.tree_item_count < TREE_DISPLAY_LIMIT:
                                    self.tree.insert(parent_id, "end", text=entry.name,
                                                   values=(self.format_size(size), mod_time))
                                    self.tree_item_count += 1
                                
                                # Update totals
                                self.total_files += 1
                                self.total_size += size
                                self.file_categories[category]["total_size"] += size
                                
                                # Add to category files list
                                self.file_categories[category]["files"].append({
                                    "path": entry.path,
                                    "size": size
                                })
                                
                                # Batch UI updates for better performance
                                if self.total_files % UI_UPDATE_BATCH_SIZE == 0:
                                    self.after(0, self._update_scan_ui)
                        
                        except (OSError, PermissionError) as e:
                            logger.warning(f"Cannot access {entry.path}: {e}")
                            continue
                        except Exception as e:
                            logger.error(f"Unexpected error scanning {entry.path}: {e}")
                            continue
            
            except (OSError, PermissionError) as e:
                logger.warning(f"Cannot access directory {path}: {e}")
                return
        
        except Exception as e:
            logger.error(f"Error scanning directory {path}: {e}")
    
    def _count_deep_files(self, path: str, category: str) -> Dict[str, int]:
        """Count files in deep directories without displaying them."""
        total_size = 0
        files_count = 0
        
        try:
            for root, dirs, files in os.walk(path):
                # Skip hidden directories
                dirs[:] = [d for d in dirs if not d.startswith('.')]
                
                for file in files:
                    if not self.scanning:
                        break
                    
                    try:
                        file_path = os.path.join(root, file)
                        file_size = os.path.getsize(file_path)
                        
                        if file_size >= MIN_FILE_SIZE_BYTES:
                            total_size += file_size
                            files_count += 1
                            
                            # Add to category data
                            self.file_categories[category]["files"].append({
                                "path": file_path,
                                "size": file_size
                            })
                    except (OSError, PermissionError):
                        continue
        except Exception as e:
            logger.error(f"Error counting files in {path}: {e}")
        
        # Update totals
        self.total_files += files_count
        self.total_size += total_size
        self.file_categories[category]["total_size"] += total_size
        
        return {'count': files_count, 'size': total_size}
    
    def _update_scan_ui(self, progress: float = None) -> None:
        """Batch update UI during scanning."""
        self.files_count_var.set(f"📄 Files: {self.total_files}")
        self.total_size_var.set(f"💾 Size: {self.format_size(self.total_size)}")
        if progress is not None:
            self.progress_var.set(progress)
    
    
    def clean_selected(self):
        # Check which categories are selected
        selected = [k for k, v in self.category_vars.items() if v.get()]
        
        if not selected:
            self._show_info("Nothing Selected", "Please select at least one category to clean.")
            return
        
        # Confirm cleaning
        total_files = sum(len(self.file_categories[k].get("files", [])) for k in selected)
        total_size = sum(self.file_categories[k].get("total_size", 0) for k in selected)
        
        if self._ask_yesno("Confirm Cleaning", 
                          f"Are you sure you want to clean {total_files} files ({self.format_size(total_size)})?\n\n"
                          "This action cannot be undone."):
            self.start_cleaning(selected)
    
    def clean_all(self):
        # Confirm cleaning all
        if self._ask_yesno("Confirm Cleaning All", 
                          f"Are you sure you want to clean all {self.total_files} files ({self.format_size(self.total_size)})?\n\n"
                          "This action cannot be undone."):
            selected = [k for k in self.file_categories.keys()]
            self.start_cleaning(selected)
    
    def start_cleaning(self, categories):
        # Update UI for cleaning state
        self.status_var.set("Cleaning...")
        self.update_status_color("cleaning")
        self.scan_button.configure(state=tk.DISABLED)
        self.clean_button.configure(state=tk.DISABLED)
        self.clean_all_button.configure(state=tk.DISABLED)
        self.close_button.configure(state=tk.DISABLED)
        self.progress_var.set(0)
        self.cleaning = True
        
        # Reset cleaning stats
        self.cleaned_files = 0
        self.cleaned_size = 0
        
        # Start cleaning thread
        clean_thread = threading.Thread(target=self.clean_files, args=(categories,))
        clean_thread.daemon = True
        clean_thread.start()
    
    def clean_files(self, categories: List[str]) -> None:
        """Optimized file cleaning with parallel deletion for faster performance."""
        try:
            # Calculate total files to clean
            total_files = sum(len(self.file_categories[k].get("files", [])) for k in categories)
            if total_files == 0:
                self.after(0, lambda: self.status_detail_var.set("No files to clean"))
                self.cleaning = False
                self.after(0, lambda: self.scan_button.configure(state=tk.NORMAL))
                return
            
            logger.info(f"Starting cleanup of {total_files} files")
            
            # Collect all files to delete
            files_to_delete = []
            for category in categories:
                cat_data = self.file_categories[category]
                files_to_delete.extend(cat_data.get("files", []))
            
            # Use ThreadPoolExecutor for parallel deletion
            files_processed = 0
            last_ui_update = 0
            
            with ThreadPoolExecutor(max_workers=MAX_DELETION_WORKERS) as executor:
                # Submit deletion tasks
                future_to_file = {
                    executor.submit(self._delete_file, file_info): file_info 
                    for file_info in files_to_delete
                }
                
                # Process completed deletions
                for future in as_completed(future_to_file):
                    if not self.cleaning:
                        # Cancel remaining tasks
                        for f in future_to_file:
                            f.cancel()
                        break
                    
                    file_info = future_to_file[future]
                    try:
                        deleted, size = future.result()
                        if deleted:
                            self.cleaned_files += 1
                            self.cleaned_size += size
                    except Exception as e:
                        logger.error(f"Error in deletion task: {e}")
                    
                    # Update progress
                    files_processed += 1
                    progress = (files_processed / total_files) * 100
                    
                    # Batch UI updates
                    if files_processed - last_ui_update >= CLEANING_UPDATE_BATCH_SIZE or \
                       files_processed == total_files:
                        last_ui_update = files_processed
                        self.after(0, lambda p=progress, f=self.cleaned_files, s=self.cleaned_size:
                                  self._update_cleaning_ui(p, f, s))
            
            # Cleaning complete
            logger.info(f"Cleanup complete: {self.cleaned_files} files, {self.cleaned_size} bytes")
            
            self.after(0, lambda: self.progress_var.set(100))
            self.after(0, lambda: self.status_var.set("Cleaning complete"))
            self.after(0, lambda: self.update_status_color("complete"))
            self.after(0, lambda: self.status_detail_var.set(
                f"Successfully cleaned {self.cleaned_files} files ({self.format_size(self.cleaned_size)})"
            ))
            
            # Reset UI
            self.cleaning = False
            self.after(0, lambda: self.scan_button.configure(state=tk.NORMAL))
            
            # Prompt for a new scan
            self.after(100, lambda: self._prompt_rescan())
        
        except Exception as e:
            logger.error(f"Error during cleaning: {e}")
            self.after(0, lambda: self.status_var.set("Cleaning error"))
            self.after(0, lambda: self.update_status_color("error"))
            self.after(0, lambda: self.status_detail_var.set(f"Error: {str(e)}"))
            self.cleaning = False
            self.after(0, lambda: self.scan_button.configure(state=tk.NORMAL))
    
    def _delete_file(self, file_info: Dict) -> Tuple[bool, int]:
        """Delete a single file or directory. Returns (success, size)."""
        file_path = file_info["path"]
        size = file_info["size"]
        
        try:
            if not os.path.exists(file_path):
                return False, 0
            
            # Delete file or directory
            if os.path.isdir(file_path):
                shutil.rmtree(file_path, ignore_errors=True)
            else:
                os.remove(file_path)
            
            logger.debug(f"Deleted: {file_path}")
            return True, size
            
        except (OSError, PermissionError) as e:
            logger.warning(f"Cannot delete {file_path}: {e}")
            return False, 0
        except Exception as e:
            logger.error(f"Unexpected error deleting {file_path}: {e}")
            return False, 0
    
    def _update_cleaning_ui(self, progress: float, files: int, size: int) -> None:
        """Batch update UI during cleaning."""
        self.progress_var.set(progress)
        self.status_detail_var.set(
            f"Cleaned {files} files ({self.format_size(size)})"
        )
    
    def _prompt_rescan(self) -> None:
        """Prompt user to rescan after cleaning."""
        if self._ask_yesno("Cleaning Complete", 
                          f"Successfully cleaned {self.cleaned_files} files ({self.format_size(self.cleaned_size)}).\n\n"
                          "Would you like to scan again?"):
            self.after(500, self.start_scan)
    
    def format_size(self, size_bytes: int) -> str:
        """Format file size in human-readable format with caching."""
        # Check cache first
        if size_bytes in self.size_cache:
            return self.size_cache[size_bytes]
        
        # Calculate formatted size
        if size_bytes < 1024:
            result = f"{size_bytes} B"
        elif size_bytes < 1024 * 1024:
            result = f"{size_bytes/1024:.1f} KB"
        elif size_bytes < 1024 * 1024 * 1024:
            result = f"{size_bytes/(1024*1024):.1f} MB"
        else:
            result = f"{size_bytes/(1024*1024*1024):.2f} GB"
        
        # Cache the result (limit cache size to prevent memory issues)
        if len(self.size_cache) < 10000:
            self.size_cache[size_bytes] = result
        
        return result
    
    def select_all_categories(self):
        for var in self.category_vars.values():
            var.set(True)
    
    def deselect_all_categories(self):
        for var in self.category_vars.values():
            var.set(False)
    
    def _center_window(self, window):
        """Center a window on the main app window."""
        window.update_idletasks()
        
        # Get main window position and size
        main_x = self.winfo_x()
        main_y = self.winfo_y()
        main_width = self.winfo_width()
        main_height = self.winfo_height()
        
        # Get dialog size
        dialog_width = window.winfo_width()
        dialog_height = window.winfo_height()
        
        # Calculate center position
        x = main_x + (main_width - dialog_width) // 2
        y = main_y + (main_height - dialog_height) // 2
        
        window.geometry(f"+{x}+{y}")
    
    def _show_info(self, title, message):
        """Show centered info messagebox."""
        # Create a temporary toplevel to get messagebox centered
        temp = tk.Toplevel(self)
        temp.withdraw()
        temp.transient(self)
        self._center_window(temp)
        messagebox.showinfo(title, message, parent=temp)
        temp.destroy()
    
    def _ask_yesno(self, title, message):
        """Show centered yes/no messagebox."""
        temp = tk.Toplevel(self)
        temp.withdraw()
        temp.transient(self)
        self._center_window(temp)
        result = messagebox.askyesno(title, message, parent=temp)
        temp.destroy()
        return result
    
    def show_about(self):
        self._show_info(
            "About iMac Cleaner Pro",
            "iMac Cleaner Pro 1.0\n\n"
            "A powerful utility to clean unwanted files from your Mac system.\n\n"
            "This application helps you identify and remove cache files, "
            "logs, temporary files and other unnecessary data to "
            "reclaim disk space and improve system performance."
        )
    
    def show_help(self):
        help_text = """
iMac Cleaner Pro - User Guide

1. Scanning:
   - Click the 'Scan Files' button to analyze your system
   - Select categories to scan using checkboxes
   - Review found files in the tree view

2. Cleaning:
   - Select categories you wish to clean
   - Click 'Clean Selected' to remove only selected categories
   - Click 'Clean All' to remove all files found during scan
   - Always review files before cleaning

3. Categories:
   - Application Cache: Cached data from applications
   - System & App Logs: Log files generated by macOS and applications
   - Temporary Files: Various temporary data
   - Downloads: Files in your Downloads folder
   - Trash Contents: Items in your Trash
   - Browser Caches: Cached data from web browsers

IMPORTANT: This application removes files permanently. Always make sure you don't need the files before cleaning.
"""
        help_window = tk.Toplevel(self)
        help_window.title("User Guide")
        help_window.geometry("600x500")
        help_window.transient(self)
        help_window.grab_set()
        
        help_frame = ttk.Frame(help_window, padding=10)
        help_frame.pack(fill=tk.BOTH, expand=True)
        
        help_title = ttk.Label(help_frame, text="iMac Cleaner Pro - User Guide", font=self.fonts["title"])
        help_title.pack(pady=(0, 10))
        
        text_widget = tk.Text(help_frame, wrap=tk.WORD, font=self.fonts["body"])
        scrollbar = ttk.Scrollbar(help_frame, orient="vertical", command=text_widget.yview)
        text_widget.configure(yscrollcommand=scrollbar.set)
        
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        text_widget.insert(tk.END, help_text)
        text_widget.configure(state="disabled")
        
        close_button = ttk.Button(help_window, text="Close", command=help_window.destroy)
        close_button.pack(pady=10)
    
    def on_close(self):
        if self.scanning or self.cleaning:
            if self._ask_yesno("Confirm Exit", 
                              "A process is currently running. Are you sure you want to exit?"):
                self.scanning = False
                self.cleaning = False
                self.destroy()
        else:
            self.destroy()

# pyinstaller --windowed --onefile --name "McCleaner" --icon=wheel.png MacCleaner.py
if __name__ == "__main__":
    app = MacCleanerApp()
    app.mainloop()