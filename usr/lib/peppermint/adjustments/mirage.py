# $HeadURL: https://fredricj@svn.berlios.de/svnroot/repos/mirageiv/branches/mirage-0.9.x/mirage.py $
# $Id: mirage.py 299 2010-07-23 12:52:26Z fredricj $

__version__ = "0.9.5.1"

__license__ = """
Mirage, a fast GTK+ Image Viewer
Copyright 2007 Scott Horowitz <stonecrest@gmail.com>

This file is part of Mirage.

Mirage is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3 of the License, or
(at your option) any later version.

Mirage is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

import pygtk
pygtk.require('2.0')
import gtk
import os, sys, getopt, ConfigParser, string, gc
import random, urllib, gobject, gettext, locale
import stat, time, subprocess, shutil, filecmp
import tempfile, socket, threading
try:
	import hashlib
	HAS_HASHLIB = True
except:
	HAS_HASHLIB= False
	import md5
try:
	import imgfuncs
	HAS_IMGFUNCS = True
except:
	HAS_IMGFUNCS = False
	print "imgfuncs.so module not found, rotating/flipping images will be disabled."
try:
	import xmouse
	HAS_XMOUSE = True
except:
	HAS_XMOUSE = False
	print "xmouse.so module not found, some screenshot capabilities will be disabled."
try:
	import gconf
except:
	pass

if gtk.gtk_version < (2, 10, 0):
	sys.stderr.write("Mirage requires GTK+ 2.10.0 or newer..\n")
	sys.exit(1)
if gtk.pygtk_version < (2, 12, 0):
	sys.stderr.write("Mirage requires PyGTK 2.12.0 or newer.\n")
	sys.exit(1)
	
def valid_int(inputstring):
	try:
		x = int(inputstring)
		return True
	except:
		return False

class Base:

	def __init__(self):
		
		gtk.gdk.threads_init()
		
		# FIX THIS! Does not work on windows and what happens if mo-files exists
		# in both dirs?
		gettext.install('mirage', '/usr/share/locale', unicode=1)
		gettext.install('mirage', '/usr/local/share/locale', unicode=1)

		# Constants
		self.open_mode_smart = 0
		self.open_mode_fit = 1
		self.open_mode_1to1 = 2
		self.open_mode_last = 3
		self.min_zoomratio = 0.02

		# Initialize vars:
		width=600
		height=400
		bgcolor_found = False
		self.simple_bgcolor = False
		# Current image:
		self.curr_img_in_list = 0
		self.currimg_name = ""
		self.currimg_width = 0
		self.currimg_height = 0
		self.currimg_pixbuf = None
		self.currimg_pixbuf_original = None
		self.currimg_zoomratio = 1
		self.currimg_is_animation = False
		# This is the actual pixbuf that is loaded in Mirage. This will
		# usually be the same as self.curr_img_in_list except for scenarios
		# like when the user presses 'next image' multiple times in a row.
		# In this case, self.curr_img_in_list will increment while
		# self.loaded_img_in_list will retain the current loaded image.
		self.loaded_img_in_list = 0
		# Next preloaded image:
		self.preloadimg_next_in_list = -1
		self.preloadimg_next_name = ""
		self.preloadimg_next_width = 0
		self.preloadimg_next_height = 0
		self.preloadimg_next_pixbuf = None
		self.preloadimg_next_pixbuf_original = None
		self.preloadimg_next_zoomratio = 1
		self.preloadimg_next_is_animation = False
		# Previous preloaded image:
		self.preloadimg_prev_in_list = -1
		self.preloadimg_prev_name = ""
		self.preloadimg_prev_width = 0
		self.preloadimg_prev_height = 0
		self.preloadimg_prev_pixbuf = None
		self.preloadimg_prev_pixbuf_original = None
		self.preloadimg_prev_zoomratio = 1
		self.preloadimg_prev_is_animation = False
		# Settings, misc:
		self.toolbar_show = True
		self.thumbpane_show = True
		self.statusbar_show = True
		self.fullscreen_mode = False
		self.opendialogpath = ""
		self.zoom_quality = gtk.gdk.INTERP_BILINEAR
		self.recursive = False
		self.verbose = False
		self.image_loaded = False
		self.open_all_images = True				# open all images in the directory(ies)
		self.use_last_dir = True
		self.last_dir = os.path.expanduser("~")
		self.fixed_dir = os.path.expanduser("~")
		self.image_list = []
		self.open_mode = self.open_mode_smart
		self.last_mode = self.open_mode_smart
		self.listwrap_mode = 0					# 0=no, 1=yes, 2=ask
		self.user_prompt_visible = False			# the "wrap?" prompt
		self.slideshow_delay = 1					# seconds
		self.slideshow_mode = False
		self.slideshow_random = False
		self.slideshow_controls_visible = False		# fullscreen slideshow controls
		self.controls_moving = False
		self.zoomvalue = 2
		self.quality_save = 90
		self.updating_adjustments = False
		self.disable_screensaver = False
		self.slideshow_in_fullscreen = False
		self.closing_app = False
		self.confirm_delete = True
		self.preloading_images = True
		self.action_names = ["Open in GIMP", "Create Thumbnail", "Create Thumbnails", "Move to Favorites"]
		self.action_shortcuts = ["<Control>e", "<Alt>t", "<Control><Alt>t", "<Control><Alt>f"]
		self.action_commands = ["gimp %F &", "convert %F -thumbnail 150x150 %Pt_%N.jpg", "convert %F -thumbnail 150x150 %Pt_%N.jpg", "mkdir -p ~/mirage-favs; mv %F ~/mirage-favs; [NEXT]"]
		self.action_batch = [False, False, True, False]
		self.onload_cmd = None
		self.searching_for_images = False
		self.preserve_aspect = True
		self.ignore_preserve_aspect_callback = False
		self.savemode = 2
		self.image_modified = False
		self.image_zoomed = False
		self.start_in_fullscreen = False
		self.running_custom_actions = False
		self.merge_id = None
		self.actionGroupCustom = None
		self.merge_id_recent = None
		self.actionGroupRecent = None
		self.open_hidden_files = False
		self.thumbnail_sizes = ["128", "96", "72", "64", "48", "32"]
		self.thumbnail_size = 128 					# Default to 128 x 128
		self.thumbnail_loaded = []
		self.thumbpane_updating = False
		self.recentfiles = ["", "", "", "", ""]
		self.screenshot_delay = 2
		self.thumbpane_bottom_coord_loaded = 0

		# Read any passed options/arguments:
		try:
			opts, args = getopt.getopt(sys.argv[1:], "hRvVsfo:", ["help", "version", "recursive", "verbose", "slideshow", "fullscreen", "onload="])
		except getopt.GetoptError:
			# print help information and exit:
			self.print_usage()
			sys.exit(2)
		# If options were passed, perform action on them.
		if opts != []:
			for o, a in opts:
				if o in ("-v", "--version"):
					self.print_version()
					sys.exit(2)
				elif o in ("-h", "--help"):
					self.print_usage()
					sys.exit(2)
				elif o in ("-R", "--recursive"):
					self.recursive = True
				elif o in ("-V", "--verbose"):
					self.verbose = True
				elif o in ("-s", "--slideshow", "-f", "--fullscreen"):
					#This will be handled later
					None
				elif o in ("-o", "--onload"):
					self.onload_cmd = a
				else:
					self.print_usage()
					sys.exit(2)


		# Determine config dir, first try the environment variable XDG_CONFIG_HOME
		# according to XDG specification and as a fallback use ~/.config/mirage
		self.config_dir = (os.getenv('XDG_CONFIG_HOME') or os.path.expanduser('~/.config')) + '/mirage'
		# Load config from disk:
		conf = ConfigParser.ConfigParser()
		if os.path.isfile(self.config_dir + '/miragerc'):
			conf.read(self.config_dir + '/miragerc')
		if conf.has_option('window', 'w'):
			width = conf.getint('window', 'w')
		if conf.has_option('window', 'h'):
			height = conf.getint('window', 'h')
		if conf.has_option('window', 'toolbar'):
			self.toolbar_show = conf.getboolean('window', 'toolbar')
		if conf.has_option('window', 'statusbar'):
			self.statusbar_show = conf.getboolean('window', 'statusbar')
		if conf.has_option('window', 'thumbpane'):
			self.thumbpane_show = conf.getboolean('window', 'thumbpane')
		if conf.has_option('prefs', 'simple-bgcolor'):
			self.simple_bgcolor = conf.getboolean('prefs', 'simple-bgcolor')
		if conf.has_option('prefs', 'bgcolor-red'):
			bgr = conf.getint('prefs', 'bgcolor-red')
			bgg = conf.getint('prefs', 'bgcolor-green')
			bgb = conf.getint('prefs', 'bgcolor-blue')
			bgcolor_found = True
			self.bgcolor = gtk.gdk.Color(red=bgr, green=bgg, blue=bgb)
		if conf.has_option('prefs', 'use_last_dir'):
			self.use_last_dir = conf.getboolean('prefs', 'use_last_dir')
		if conf.has_option('prefs', 'last_dir'):
			self.last_dir = conf.get('prefs', 'last_dir')
		if conf.has_option('prefs', 'fixed_dir'):
			self.fixed_dir = conf.get('prefs', 'fixed_dir')
		if conf.has_option('prefs', 'open_all'):
			self.open_all_images = conf.getboolean('prefs', 'open_all')
		if conf.has_option('prefs', 'hidden'):
			self.open_hidden_files = conf.getboolean('prefs', 'hidden')
		if conf.has_option('prefs', 'open_mode'):
			self.open_mode = conf.getint('prefs', 'open_mode')
		if conf.has_option('prefs', 'last_mode'):
			self.last_mode = conf.getint('prefs', 'last_mode')
		if conf.has_option('prefs', 'listwrap_mode'):
			self.listwrap_mode = conf.getint('prefs', 'listwrap_mode')
		if conf.has_option('prefs', 'slideshow_delay'):
			self.slideshow_delay = conf.getint('prefs', 'slideshow_delay')
		if conf.has_option('prefs', 'slideshow_random'):
			self.slideshow_random = conf.getboolean('prefs', 'slideshow_random')
		if conf.has_option('prefs', 'zoomquality'):
			self.zoomvalue = conf.getint('prefs', 'zoomquality')
			if int(round(self.zoomvalue, 0)) == 0:
				self.zoom_quality = gtk.gdk.INTERP_NEAREST
			elif int(round(self.zoomvalue, 0)) == 1:
				self.zoom_quality = gtk.gdk.INTERP_TILES
			elif int(round(self.zoomvalue, 0)) == 2:
				self.zoom_quality = gtk.gdk.INTERP_BILINEAR
			elif int(round(self.zoomvalue, 0)) == 3:
				self.zoom_quality = gtk.gdk.INTERP_HYPER
		if conf.has_option('prefs', 'quality_save'):
			self.quality_save = conf.getint('prefs', 'quality_save')
		if conf.has_option('prefs', 'disable_screensaver'):
			self.disable_screensaver = conf.getboolean('prefs', 'disable_screensaver')
		if conf.has_option('prefs', 'slideshow_in_fullscreen'):
			self.slideshow_in_fullscreen = conf.getboolean('prefs', 'slideshow_in_fullscreen')
		if conf.has_option('prefs', 'preloading_images'):
			self.preloading_images = conf.getboolean('prefs', 'preloading_images')
		if conf.has_option('prefs', 'thumbsize'):
			self.thumbnail_size = conf.getint('prefs', 'thumbsize')
		if conf.has_option('prefs', 'screenshot_delay'):
			self.screenshot_delay = conf.getint('prefs', 'screenshot_delay')
		if conf.has_option('actions', 'num_actions'):
			num_actions = conf.getint('actions', 'num_actions')
			self.action_names = []
			self.action_commands = []
			self.action_shortcuts = []
			self.action_batch = []
			for i in range(num_actions):
				if conf.has_option('actions', 'names[' + str(i) + ']') and conf.has_option('actions', 'commands[' + str(i) + ']') and conf.has_option('actions', 'shortcuts[' + str(i) + ']') and conf.has_option('actions', 'batch[' + str(i) + ']'):
					self.action_names.append(conf.get('actions', 'names[' + str(i) + ']'))
					self.action_commands.append(conf.get('actions', 'commands[' + str(i) + ']'))
					self.action_shortcuts.append(conf.get('actions', 'shortcuts[' + str(i) + ']'))
					self.action_batch.append(conf.getboolean('actions', 'batch[' + str(i) + ']'))
		if conf.has_option('prefs', 'savemode'):
			self.savemode = conf.getint('prefs', 'savemode')
		if conf.has_option('prefs', 'start_in_fullscreen'):
			self.start_in_fullscreen = conf.getboolean('prefs', 'start_in_fullscreen')
		if conf.has_option('prefs', 'confirm_delete'):
			self.confirm_delete = conf.getboolean('prefs', 'confirm_delete')
		self.recentfiles = []
		if conf.has_option('recent', 'num_recent'):
			num_recent = conf.getint('recent', 'num_recent')
			for i in range(num_recent):
				self.recentfiles.append('')
				if conf.has_option('recent', 'urls[' + str(i) + ',0]'):
					self.recentfiles[i] = conf.get('recent', 'urls[' + str(i) + ',0]')
		# slideshow_delay is the user's preference, whereas curr_slideshow_delay is
		# the current delay (which can be changed without affecting the 'default')
		self.curr_slideshow_delay = self.slideshow_delay
		# Same for randomization:
		self.curr_slideshow_random = self.slideshow_random

		# Read accel_map file, if it exists
		if os.path.isfile(self.config_dir + '/accel_map'):
			gtk.accel_map_load(self.config_dir + '/accel_map')
		
		# Directory/ies in which to find application images/pixmaps
		self.resource_path_list = False
		
		self.blank_image = gtk.gdk.pixbuf_new_from_file(self.find_path("mirage_blank.png"))

		# Define the main menubar and toolbar:
		factory = gtk.IconFactory()
		iconname = 'stock_leave-fullscreen.png'
		iconname2 = 'stock_fullscreen.png'
		leave_fullscreen_icon_path = self.find_path(iconname)
		pixbuf = gtk.gdk.pixbuf_new_from_file(leave_fullscreen_icon_path)
		iconset = gtk.IconSet(pixbuf)
		factory.add('leave-fullscreen', iconset)
		factory.add_default()
		fullscreen_icon_path = self.find_path(iconname2)
		pixbuf = gtk.gdk.pixbuf_new_from_file(fullscreen_icon_path)
		iconset = gtk.IconSet(pixbuf)
		factory.add('fullscreen', iconset)
		factory.add_default()
		try:
			test = gtk.Button("", gtk.STOCK_LEAVE_FULLSCREEN)
			leave_fullscreen_icon = gtk.STOCK_LEAVE_FULLSCREEN
			fullscreen_icon = gtk.STOCK_FULLSCREEN
		except:
			# This will allow gtk 2.6 users to run Mirage
			leave_fullscreen_icon = 'leave-fullscreen'
			fullscreen_icon = 'fullscreen'
		actions = (
			('FileMenu', None, _('_File')),
			('EditMenu', None, _('_Edit')),
			('ViewMenu', None, _('_View')),
			('GoMenu', None, _('_Go')),
			('HelpMenu', None, _('_Help')),
			('ActionSubMenu', None, _('Custom _Actions')),
			('Open Image', gtk.STOCK_FILE, _('_Open Image...'), '<Ctrl>O', _('Open Image'), self.open_file),
			('Open Remote Image', gtk.STOCK_NETWORK, _('Open _Remote image...'), None, _('Open Remote Image'), self.open_file_remote),
			('Open Folder', gtk.STOCK_DIRECTORY, _('Open _Folder...'), '<Ctrl>F', _('Open Folder'), self.open_folder),
			('Save', gtk.STOCK_SAVE, _('_Save Image'), '<Ctrl>S', _('Save Image'), self.save_image),
			('Save As', gtk.STOCK_SAVE, _('Save Image _As...'), '<Shift><Ctrl>S', _('Save Image As'), self.save_image_as),
			('Crop', None, _('_Crop...'), None, _('Crop Image'), self.crop_image),
			('Resize', None, _('R_esize...'), None, _('Resize Image'), self.resize_image),
			('Saturation', None, _('_Saturation...'), None, _('Modify saturation'), self.saturation),
			('Quit', gtk.STOCK_QUIT, _('_Quit'), '<Ctrl>Q', _('Quit'), self.exit_app),
			('Previous Image', gtk.STOCK_GO_BACK, _('_Previous Image'), 'Left', _('Previous Image'), self.goto_prev_image),
			('Next Image', gtk.STOCK_GO_FORWARD, _('_Next Image'), 'Right', _('Next Image'), self.goto_next_image),
			('Previous2', gtk.STOCK_GO_BACK, _('_Previous'), 'Left', _('Previous'), self.goto_prev_image),
			('Next2', gtk.STOCK_GO_FORWARD, _('_Next'), 'Right', _('Next'), self.goto_next_image),
			('Random Image', None, _('_Random Image'), 'R', _('Random Image'), self.goto_random_image),
			('First Image', gtk.STOCK_GOTO_FIRST, _('_First Image'), 'Home', _('First Image'), self.goto_first_image),
			('Last Image', gtk.STOCK_GOTO_LAST, _('_Last Image'), 'End', _('Last Image'), self.goto_last_image),
			('In', gtk.STOCK_ZOOM_IN, _('Zoom _In'), '<Ctrl>Up', _('Zoom In'), self.zoom_in),
			('Out', gtk.STOCK_ZOOM_OUT, _('Zoom _Out'), '<Ctrl>Down', _('Zoom Out'), self.zoom_out),
			('Fit', gtk.STOCK_ZOOM_FIT, _('Zoom To _Fit'), '<Ctrl>0', _('Fit'), self.zoom_to_fit_window_action),
			('1:1', gtk.STOCK_ZOOM_100, _('_1:1'), '<Ctrl>1', _('1:1'), self.zoom_1_to_1_action),
			('Rotate Left', None, _('Rotate _Left'), '<Ctrl>Left', _('Rotate Left'), self.rotate_left),
			('Rotate Right', None, _('Rotate _Right'), '<Ctrl>Right', _('Rotate Right'), self.rotate_right),
			('Flip Vertically', None, _('Flip _Vertically'), '<Ctrl>V', _('Flip Vertically'), self.flip_image_vert),
			('Flip Horizontally', None, _('Flip _Horizontally'), '<Ctrl>H', _('Flip Horizontally'), self.flip_image_horiz),
			('About', gtk.STOCK_ABOUT, _('_About'), None, _('About'), self.show_about),
			('Contents', gtk.STOCK_HELP, _('_Contents'), 'F1', _('Contents'), self.show_help),
			('Preferences', gtk.STOCK_PREFERENCES, _('_Preferences...'), '<Ctrl>P', _('Preferences'), self.show_prefs),
			('Full Screen', fullscreen_icon, _('_Full Screen'), 'F11', _('Full Screen'), self.enter_fullscreen),
			('Exit Full Screen', leave_fullscreen_icon, _('E_xit Full Screen'), None, _('Exit Full Screen'), self.leave_fullscreen),
			('Start Slideshow', gtk.STOCK_MEDIA_PLAY, _('_Start Slideshow'), 'F5', _('Start Slideshow'), self.toggle_slideshow),
			('Stop Slideshow', gtk.STOCK_MEDIA_STOP, _('_Stop Slideshow'), 'F5', _('Stop Slideshow'), self.toggle_slideshow),
			('Delete Image', gtk.STOCK_DELETE, _('_Delete...'), 'Delete', _('Delete Image'), self.delete_image),
			('Rename Image', None, _('Re_name...'), 'F2', _('Rename Image'), self.rename_image),
			('Take Screenshot', None, _('_Take Screenshot...'), None, _('Take Screenshot'), self.screenshot),
			('Properties', gtk.STOCK_PROPERTIES, _('_Properties...'), None, _('Properties'), self.show_properties),
			('Custom Actions', None, _('_Configure...'), None, _('Custom Actions'), self.show_custom_actions),
			('MiscKeysMenuHidden', None, 'Keys'),
			('Escape', None, '', 'Escape', _('Exit Full Screen'), self.leave_fullscreen),
			('Minus', None, '', 'minus', _('Zoom Out'), self.zoom_out),
			('Plus', None, '', 'plus', _('Zoom In'), self.zoom_in),
			('Equal', None, '', 'equal', _('Zoom In'), self.zoom_in),
			('Space', None, '', 'space', _('Next Image'), self.goto_next_image),
			('Ctrl-KP_Insert', None, '', '<Ctrl>KP_Insert', _('Fit'), self.zoom_to_fit_window_action),
			('Ctrl-KP_End', None, '', '<Ctrl>KP_End', _('1:1'), self.zoom_1_to_1_action),
			('Ctrl-KP_Subtract', None, '', '<Ctrl>KP_Subtract', _('Zoom Out'), self.zoom_out),
			('Ctrl-KP_Add', None, '', '<Ctrl>KP_Add', _('Zoom In'), self.zoom_in),
			('Ctrl-KP_0', None, '', '<Ctrl>KP_0', _('Fit'), self.zoom_to_fit_window_action),
			('Ctrl-KP_1', None, '', '<Ctrl>KP_1', _('1:1'), self.zoom_1_to_1_action),
			('Full Screen Key', None, '', '<Shift>Return', None, self.enter_fullscreen),
			('Prev', None, '', 'Up', _('Previous Image'), self.goto_prev_image),
			('Next', None, '', 'Down', _('Next Image'), self.goto_next_image),
			('PgUp', None, '', 'Page_Up', _('Previous Image'), self.goto_prev_image),
			('PgDn', None, '', 'Page_Down', _('Next Image'), self.goto_next_image),
			('BackSpace', None, '', 'BackSpace', _('Previous Image'), self.goto_prev_image),
			('OriginalSize', None, '', '1', _('1:1'), self.zoom_1_to_1_action),
			('ZoomIn', None, '', 'KP_Add', _('Zoom In'), self.zoom_in),
			('ZoomOut', None, '', 'KP_Subtract', _('Zoom Out'), self.zoom_out)
			)
		toggle_actions = (
			('Status Bar', None, _('_Status Bar'), None, _('Status Bar'), self.toggle_status_bar, self.statusbar_show),
			('Toolbar', None, _('_Toolbar'), None, _('Toolbar'), self.toggle_toolbar, self.toolbar_show),
			('Thumbnails Pane', None, _('Thumbnails _Pane'), None, _('Thumbnails Pane'), self.toggle_thumbpane, self.thumbpane_show)
				)

		# Populate keys[]:
		self.keys=[]
		for i in range(len(actions)):
			if len(actions[i]) > 3:
				if actions[i][3] != None:
					self.keys.append([actions[i][4], actions[i][3]])

		uiDescription = """
			<ui>
			  <popup name="Popup">
			    <menuitem action="Next Image"/>
			    <menuitem action="Previous Image"/>
			    <separator name="FM1"/>
			    <menuitem action="Out"/>
			    <menuitem action="In"/>
			    <menuitem action="1:1"/>
			    <menuitem action="Fit"/>
			    <separator name="FM4"/>
			    <menuitem action="Start Slideshow"/>
			    <menuitem action="Stop Slideshow"/>
			    <separator name="FM3"/>
			    <menuitem action="Exit Full Screen"/>
			    <menuitem action="Full Screen"/>
			  </popup>
			  <menubar name="MainMenu">
			    <menu action="FileMenu">
			      <menuitem action="Open Image"/>
			      <menuitem action="Open Folder"/>
			      <menuitem action="Open Remote Image"/>
			      <separator name="FM1"/>
			      <menuitem action="Save"/>
			      <menuitem action="Save As"/>
			      <separator name="FM2"/>
			      <menuitem action="Take Screenshot"/>
			      <separator name="FM3"/>
			      <menuitem action="Properties"/>
			      <separator name="FM4"/>
			      <placeholder name="Recent Files">
			      </placeholder>
			      <separator name="FM5"/>
			      <menuitem action="Quit"/>
			    </menu>
			    <menu action="EditMenu">
			      <menuitem action="Rotate Left"/>
			      <menuitem action="Rotate Right"/>
			      <menuitem action="Flip Vertically"/>
			      <menuitem action="Flip Horizontally"/>
			      <separator name="FM1"/>
			      <menuitem action="Crop"/>
			      <menuitem action="Resize"/>
			      <menuitem action="Saturation"/>
			      <separator name="FM2"/>
			      <menuitem action="Rename Image"/>
			      <menuitem action="Delete Image"/>
			      <separator name="FM3"/>
			      <menu action="ActionSubMenu">
    			    <separator name="FM4" position="bot"/>
    			    <menuitem action="Custom Actions" position="bot"/>
			      </menu>
			      <menuitem action="Preferences"/>
			    </menu>
			    <menu action="ViewMenu">
			      <menuitem action="Out"/>
			      <menuitem action="In"/>
			      <menuitem action="1:1"/>
			      <menuitem action="Fit"/>
			      <separator name="FM2"/>
			      <menuitem action="Toolbar"/>
			      <menuitem action="Thumbnails Pane"/>
			      <menuitem action="Status Bar"/>
			      <separator name="FM1"/>
			      <menuitem action="Full Screen"/>
			   </menu>
			    <menu action="GoMenu">
			      <menuitem action="Next Image"/>
			      <menuitem action="Previous Image"/>
			      <menuitem action="Random Image"/>
			      <separator name="FM1"/>
			      <menuitem action="First Image"/>
			      <menuitem action="Last Image"/>
			      <separator name="FM2"/>
			      <menuitem action="Start Slideshow"/>
			      <menuitem action="Stop Slideshow"/>
			    </menu>
			    <menu action="HelpMenu">
			      <menuitem action="Contents"/>
			      <menuitem action="About"/>
			    </menu>
			    <menu action="MiscKeysMenuHidden">
			      <menuitem action="Minus"/>
			      <menuitem action="Escape"/>
			      <menuitem action="Plus"/>
			      <menuitem action="Equal"/>
			      <menuitem action="Space"/>
			      <menuitem action="Ctrl-KP_Insert"/>
			      <menuitem action="Ctrl-KP_End"/>
			      <menuitem action="Ctrl-KP_Subtract"/>
			      <menuitem action="Ctrl-KP_Add"/>
			      <menuitem action="Ctrl-KP_0"/>
			      <menuitem action="Ctrl-KP_1"/>
			      <menuitem action="Full Screen Key"/>
			      <menuitem action="Prev"/>
			      <menuitem action="Next"/>
			      <menuitem action="PgUp"/>
			      <menuitem action="PgDn"/>
			      <menuitem action="OriginalSize"/>	
			      <menuitem action="BackSpace"/>
			      <menuitem action="ZoomIn"/>
			      <menuitem action="ZoomOut"/>
			    </menu>
			  </menubar>
			  <toolbar name="MainToolbar">
			    <toolitem action="Open Image"/>
			    <separator name="FM1"/>
			    <toolitem action="Previous2"/>
			    <toolitem action="Next2"/>
			    <separator name="FM2"/>
			    <toolitem action="Out"/>
			    <toolitem action="In"/>
			    <toolitem action="1:1"/>
			    <toolitem action="Fit"/>
			  </toolbar>
			</ui>
			"""

		# Create interface
		self.window = gtk.Window(gtk.WINDOW_TOPLEVEL)
		self.update_title()
		icon_path = self.find_path('mirage.png')
		try:
			gtk.window_set_default_icon_from_file(icon_path)
		except:
			pass
		vbox = gtk.VBox(False, 0)
		self.UIManager = gtk.UIManager()
		actionGroup = gtk.ActionGroup('Actions')
		actionGroup.add_actions(actions)
		actionGroup.add_toggle_actions(toggle_actions)
		self.UIManager.insert_action_group(actionGroup, 0)
		self.UIManager.add_ui_from_string(uiDescription)
		self.refresh_custom_actions_menu()
		self.refresh_recent_files_menu()
		self.window.add_accel_group(self.UIManager.get_accel_group())
		self.menubar = self.UIManager.get_widget('/MainMenu')
		vbox.pack_start(self.menubar, False, False, 0)
		self.toolbar = self.UIManager.get_widget('/MainToolbar')
		vbox.pack_start(self.toolbar, False, False, 0)
		self.layout = gtk.Layout()
		self.vscroll = gtk.VScrollbar(None)
		self.vscroll.set_adjustment(self.layout.get_vadjustment())
		self.hscroll = gtk.HScrollbar(None)
		self.hscroll.set_adjustment(self.layout.get_hadjustment())
		self.table = gtk.Table(3, 2, False)

		self.thumblist = gtk.ListStore(gtk.gdk.Pixbuf)
		self.thumbpane = gtk.TreeView(self.thumblist)
		self.thumbcolumn = gtk.TreeViewColumn(None)
		self.thumbcell = gtk.CellRendererPixbuf()
		self.thumbcolumn.set_sizing(gtk.TREE_VIEW_COLUMN_FIXED)
		self.thumbpane_set_size()
		self.thumbpane.append_column(self.thumbcolumn)
		self.thumbcolumn.pack_start(self.thumbcell, True)
		self.thumbcolumn.set_attributes(self.thumbcell, pixbuf=0)
		self.thumbpane.get_selection().set_mode(gtk.SELECTION_SINGLE)
		self.thumbpane.set_headers_visible(False)
		self.thumbpane.set_property('can-focus', False)
		self.thumbscroll = gtk.ScrolledWindow()
		self.thumbscroll.set_policy(gtk.POLICY_NEVER, gtk.POLICY_ALWAYS)
		self.thumbscroll.add(self.thumbpane)
		
		self.table.attach(self.thumbscroll, 0, 1, 0, 1, 0, gtk.FILL|gtk.EXPAND, 0, 0)
		self.table.attach(self.layout, 1, 2, 0, 1, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		self.table.attach(self.hscroll, 1, 2, 1, 2, gtk.FILL|gtk.SHRINK, gtk.FILL|gtk.SHRINK, 0, 0)
		self.table.attach(self.vscroll, 2, 3, 0, 1, gtk.FILL|gtk.SHRINK, gtk.FILL|gtk.SHRINK, 0, 0)
		vbox.pack_start(self.table, True, True, 0)
		if not bgcolor_found:
			self.bgcolor = gtk.gdk.Color(0, 0, 0) # Default to black
		if self.simple_bgcolor:
			self.layout.modify_bg(gtk.STATE_NORMAL, None)
		else:
			self.layout.modify_bg(gtk.STATE_NORMAL, self.bgcolor)
		self.imageview = gtk.Image()
		self.layout.add(self.imageview)

		self.statusbar = gtk.Statusbar()
		self.statusbar2 = gtk.Statusbar()
		self.statusbar.set_has_resize_grip(False)
		self.statusbar2.set_has_resize_grip(True)
		self.statusbar2.set_size_request(200, -1)
		hbox_statusbar = gtk.HBox()
		hbox_statusbar.pack_start(self.statusbar, expand=True)
		hbox_statusbar.pack_start(self.statusbar2, expand=False)
		vbox.pack_start(hbox_statusbar, False, False, 0)
		self.window.add(vbox)
		self.window.set_property('allow-shrink', False)
		self.window.set_default_size(width,height)
		
		# Slideshow control:
		self.slideshow_window = gtk.Window(gtk.WINDOW_POPUP)
		self.slideshow_controls = gtk.HBox()
		self.ss_back = gtk.Button()
		self.ss_back.add(gtk.image_new_from_stock(gtk.STOCK_GO_BACK, gtk.ICON_SIZE_BUTTON))
		self.ss_back.set_property('can-focus', False)
		self.ss_back.connect('clicked', self.goto_prev_image)
		self.ss_start = gtk.Button("", gtk.STOCK_MEDIA_PLAY)
		self.ss_start.get_child().get_child().get_children()[1].set_text('')
		self.ss_start.set_property('can-focus', False)
		self.ss_start.connect('clicked', self.toggle_slideshow)
		self.ss_stop = gtk.Button("", gtk.STOCK_MEDIA_STOP)
		self.ss_stop.get_child().get_child().get_children()[1].set_text('')
		self.ss_stop.set_property('can-focus', False)
		self.ss_stop.connect('clicked', self.toggle_slideshow)
		self.ss_forward = gtk.Button("", gtk.STOCK_GO_FORWARD)
		self.ss_forward.get_child().get_child().get_children()[1].set_text('')
		self.ss_forward.set_property('can-focus', False)
		self.ss_forward.connect('clicked', self.goto_next_image)
		self.slideshow_controls.pack_start(self.ss_back, False, False, 0)
		self.slideshow_controls.pack_start(self.ss_start, False, False, 0)
		self.slideshow_controls.pack_start(self.ss_stop, False, False, 0)
		self.slideshow_controls.pack_start(self.ss_forward, False, False, 0)
		self.slideshow_window.add(self.slideshow_controls)
		if self.simple_bgcolor:
			self.slideshow_window.modify_bg(gtk.STATE_NORMAL, None)
		else:
			self.slideshow_window.modify_bg(gtk.STATE_NORMAL, self.bgcolor)
		self.slideshow_window2 = gtk.Window(gtk.WINDOW_POPUP)
		self.slideshow_controls2 = gtk.HBox()
		try:
			self.ss_exit = gtk.Button("", gtk.STOCK_LEAVE_FULLSCREEN)
			self.ss_exit.get_child().get_child().get_children()[1].set_text('')
		except:
			self.ss_exit = gtk.Button()
			self.ss_exit.set_image(gtk.image_new_from_stock('leave-fullscreen', gtk.ICON_SIZE_MENU))
		self.ss_exit.set_property('can-focus', False)
		self.ss_exit.connect('clicked', self.leave_fullscreen)
		self.ss_randomize = gtk.ToggleButton()
		icon_path = self.find_path('stock_shuffle.png')
		try:
			pixbuf = gtk.gdk.pixbuf_new_from_file(icon_path)
			iconset = gtk.IconSet(pixbuf)
			factory.add('stock-shuffle', iconset)
			factory.add_default()
			self.ss_randomize.set_image(gtk.image_new_from_stock('stock-shuffle', gtk.ICON_SIZE_MENU))
		except:
			self.ss_randomize.set_label("Rand")
		self.ss_randomize.connect('toggled', self.random_changed)
		
		spin_adj = gtk.Adjustment(self.slideshow_delay, 0, 50000, 1,100, 0)
		self.ss_delayspin = gtk.SpinButton(spin_adj, 1.0, 0)
		self.ss_delayspin.set_numeric(True)
		self.ss_delayspin.connect('changed', self.delay_changed)
		self.slideshow_controls2.pack_start(self.ss_randomize, False, False, 0)
		self.slideshow_controls2.pack_start(self.ss_delayspin, False, False, 0)
		self.slideshow_controls2.pack_start(self.ss_exit, False, False, 0)
		self.slideshow_window2.add(self.slideshow_controls2)
		if self.simple_bgcolor:
			self.slideshow_window2.modify_bg(gtk.STATE_NORMAL, None)
		else:
			self.slideshow_window2.modify_bg(gtk.STATE_NORMAL, self.bgcolor)

		# Connect signals
		self.window.connect("delete_event", self.delete_event)
		self.window.connect("destroy", self.destroy)
		self.window.connect("size-allocate", self.window_resized)
		self.window.connect('key-press-event', self.topwindow_keypress)
		self.toolbar.connect('focus', self.toolbar_focused)
		self.layout.drag_dest_set(gtk.DEST_DEFAULT_HIGHLIGHT | gtk.DEST_DEFAULT_DROP, [("text/uri-list", 0, 80)], gtk.gdk.ACTION_DEFAULT)
		self.layout.connect('drag_motion', self.motion_cb)
		self.layout.connect('drag_data_received', self.drop_cb)
		self.layout.add_events(gtk.gdk.KEY_PRESS_MASK | gtk.gdk.POINTER_MOTION_MASK | gtk.gdk.BUTTON_PRESS_MASK | gtk.gdk.BUTTON_MOTION_MASK | gtk.gdk.SCROLL_MASK)
		self.layout.connect("scroll-event", self.mousewheel_scrolled)
		self.layout.add_events(gtk.gdk.BUTTON_PRESS_MASK | gtk.gdk.KEY_PRESS_MASK)
		self.layout.connect("button_press_event", self.button_pressed)
		self.layout.add_events(gtk.gdk.POINTER_MOTION_MASK | gtk.gdk.POINTER_MOTION_HINT_MASK | gtk.gdk.BUTTON_RELEASE_MASK)
		self.layout.connect("motion-notify-event", self.mouse_moved)
		self.layout.connect("button-release-event", self.button_released)
		self.imageview.connect("expose-event", self.expose_event)
		self.thumb_sel_handler = self.thumbpane.get_selection().connect('changed', self.thumbpane_selection_changed)
		self.thumb_scroll_handler = self.thumbscroll.get_vscrollbar().connect("value-changed", self.thumbpane_scrolled)

		# Since GNOME does its own thing for the toolbar style...
		# Requires gnome-python installed to work (but optional)
		try:
			client = gconf.client_get_default()
			style = client.get_string('/desktop/gnome/interface/toolbar_style')
			if style == "both":
				self.toolbar.set_style(gtk.TOOLBAR_BOTH)
			elif style == "both-horiz":
				self.toolbar.set_style(gtk.TOOLBAR_BOTH_HORIZ)
			elif style == "icons":
				self.toolbar.set_style(gtk.TOOLBAR_ICONS)
			elif style == "text":
				self.toolbar.set_style(gtk.TOOLBAR_TEXT)
			client.add_dir("/desktop/gnome/interface", gconf.CLIENT_PRELOAD_NONE)
			client.notify_add("/desktop/gnome/interface/toolbar_style", self.gconf_key_changed)
		except:
			pass

		# Show GUI:
		if not self.toolbar_show:
			self.toolbar.set_property('visible', False)
			self.toolbar.set_no_show_all(True)
		if not self.statusbar_show:
			self.statusbar.set_property('visible', False)
			self.statusbar.set_no_show_all(True)
			self.statusbar2.set_property('visible', False)
			self.statusbar2.set_no_show_all(True)
		if not self.thumbpane_show:
			self.thumbscroll.set_property('visible', False)
			self.thumbscroll.set_no_show_all(True)
		self.hscroll.set_no_show_all(True)
		self.vscroll.set_no_show_all(True)
		go_into_fullscreen = False
		if opts != []:
			for o, a in opts:
				if (o in ("-f", "--fullscreen")) or ((o in ("-s", "--slideshow")) and self.slideshow_in_fullscreen):
					go_into_fullscreen = True
		if go_into_fullscreen or self.start_in_fullscreen:
			self.enter_fullscreen(None)
			self.statusbar.set_no_show_all(True)
			self.statusbar2.set_no_show_all(True)
			self.toolbar.set_no_show_all(True)
			self.menubar.set_no_show_all(True)
			self.thumbscroll.set_no_show_all(True)
		self.window.show_all()
		self.ss_exit.set_size_request(self.ss_start.size_request()[0], self.ss_stop.size_request()[1])
		self.ss_randomize.set_size_request(self.ss_start.size_request()[0], -1)
		self.ss_start.set_size_request(self.ss_start.size_request()[0]*2, -1)
		self.ss_stop.set_size_request(self.ss_stop.size_request()[0]*2, -1)
		self.UIManager.get_widget('/Popup/Exit Full Screen').hide()
		self.layout.set_flags(gtk.CAN_FOCUS)
		self.window.set_focus(self.layout)
		
		#sets the visibility of some menu entries
		self.set_slideshow_sensitivities()
		self.UIManager.get_widget('/MainMenu/MiscKeysMenuHidden').set_property('visible', False)
		if opts != []:
			for o, a in opts:
				if o in ("-f", "--fullscreen"):
					self.UIManager.get_widget('/Popup/Exit Full Screen').show()

		# If arguments (filenames) were passed, try to open them:
		self.image_list = []
		if args != []:
			for i in range(len(args)):
				args[i] = urllib.url2pathname(args[i])
			self.expand_filelist_and_load_image(args)
		else:
			self.set_go_sensitivities(False)
			self.set_image_sensitivities(False)

		if opts != []:
			for o, a in opts:
				if o in ("-s", "--slideshow"):
					self.toggle_slideshow(None)

	def refresh_recent_files_menu(self):
		if self.merge_id_recent:
			self.UIManager.remove_ui(self.merge_id_recent)
		if self.actionGroupRecent:
			self.UIManager.remove_action_group(self.actionGroupRecent)
			self.actionGroupRecent = None
		self.actionGroupRecent = gtk.ActionGroup('RecentFiles')
		self.UIManager.ensure_update()
		for i in range(len(self.recentfiles)):
			if len(self.recentfiles[i]) > 0:
				filename = self.recentfiles[i].split("/")[-1]
				if len(filename) > 0:
					if len(filename) > 27:
						# Replace end of file name (excluding extension) with ..
						try:
							menu_name = filename[:25] + '..' + os.path.splitext(filename)[1]
						except:
							menu_name = filename[0]
					else:
						menu_name = filename
					menu_name = menu_name.replace('_','__')
					action = [(str(i), None, menu_name, '<Alt>' + str(i+1), None, self.recent_action_click)]
					self.actionGroupRecent.add_actions(action)
		uiDescription = """
			<ui>
			  <menubar name="MainMenu">
			    <menu action="FileMenu">
			      <placeholder name="Recent Files">
			"""
		for i in range(len(self.recentfiles)):
			if len(self.recentfiles[i]) > 0:
				uiDescription = uiDescription + """<menuitem action=\"""" + str(i) + """\"/>"""
		uiDescription = uiDescription + """</placeholder></menu></menubar></ui>"""
		self.merge_id_recent = self.UIManager.add_ui_from_string(uiDescription)
		self.UIManager.insert_action_group(self.actionGroupRecent, 0)
		self.UIManager.get_widget('/MainMenu/MiscKeysMenuHidden').set_property('visible', False)

	def refresh_custom_actions_menu(self):
		if self.merge_id:
			self.UIManager.remove_ui(self.merge_id)
		if self.actionGroupCustom:
			self.UIManager.remove_action_group(self.actionGroupCustom)
			self.actionGroupCustom = None
		self.actionGroupCustom = gtk.ActionGroup('CustomActions')
		self.UIManager.ensure_update()
		for i in range(len(self.action_names)):
			action = [(self.action_names[i], None, self.action_names[i], self.action_shortcuts[i], None, self.custom_action_click)]
			self.actionGroupCustom.add_actions(action)
		uiDescription = """
			<ui>
			  <menubar name="MainMenu">
			    <menu action="EditMenu">
			      <menu action="ActionSubMenu">
			"""
		for i in range(len(self.action_names)):
			uiDescription = uiDescription + """<menuitem action=\"""" + self.action_names[len(self.action_names)-i-1].replace('&','&amp;') + """\" position="top"/>"""
		uiDescription = uiDescription + """</menu></menu></menubar></ui>"""
		self.merge_id = self.UIManager.add_ui_from_string(uiDescription)
		self.UIManager.insert_action_group(self.actionGroupCustom, 0)
		self.UIManager.get_widget('/MainMenu/MiscKeysMenuHidden').set_property('visible', False)
		
	def thumbpane_update_images(self, clear_first=False, force_upto_imgnum=-1):
		self.stop_now = False
		# When first populating the thumbpane, make sure we go up to at least
		# force_upto_imgnum so that we can show this image selected:
		if clear_first:
			self.thumbpane_clear_list()
		# Load all images up to the bottom ofo the visible thumbpane rect:
		rect = self.thumbpane.get_visible_rect()
		bottom_coord = rect.y + rect.height + self.thumbnail_size
		if bottom_coord > self.thumbpane_bottom_coord_loaded:
			self.thumbpane_bottom_coord_loaded = bottom_coord
		# update images:
		if not self.thumbpane_updating:
			thread = threading.Thread(target=self.thumbpane_update_pending_images, args=(force_upto_imgnum, None))
			thread.setDaemon(True)
			thread.start()

	def thumbpane_create_dir(self):
		if not os.path.exists(os.path.expanduser('~/.thumbnails/')):
			os.mkdir(os.path.expanduser('~/.thumbnails/'))
		if not os.path.exists(os.path.expanduser('~/.thumbnails/normal/')):
			os.mkdir(os.path.expanduser('~/.thumbnails/normal/'))

	def thumbpane_update_pending_images(self, force_upto_imgnum, foo):
		self.thumbpane_updating = True
		self.thumbpane_create_dir()
		# Check to see if any images need their thumbnails generated.
		curr_coord = 0
		imgnum = 0
		while curr_coord < self.thumbpane_bottom_coord_loaded or imgnum <= force_upto_imgnum:
			if self.closing_app or self.stop_now or not self.thumbpane_show:
				break
			if imgnum >= len(self.image_list):
				break
			self.thumbpane_set_image(self.image_list[imgnum], imgnum)
			curr_coord += self.thumbpane.get_background_area((imgnum,),self.thumbcolumn).height
			if force_upto_imgnum == imgnum:
				# Verify that the user hasn't switched images while we're loading thumbnails:
				if force_upto_imgnum == self.curr_img_in_list:
					gobject.idle_add(self.thumbpane_select, force_upto_imgnum)
			imgnum += 1
		self.thumbpane_updating = False
	
	def thumbpane_clear_list(self):
		self.thumbpane_bottom_coord_loaded = 0
		self.thumbscroll.get_vscrollbar().handler_block(self.thumb_scroll_handler)
		self.thumblist.clear()
		self.thumbscroll.get_vscrollbar().handler_unblock(self.thumb_scroll_handler)
		for image in self.image_list:
			blank_pix = self.get_blank_pix_for_image(image)
			self.thumblist.append([blank_pix])
		self.thumbnail_loaded = [False]*len(self.image_list)

	def thumbpane_set_image(self, image_name, imgnum, force_update=False):
		if self.thumbpane_show:
			if not self.thumbnail_loaded[imgnum] or force_update:
				filename, thumbfile = self.thumbnail_get_name(image_name)
				pix = self.thumbpane_get_pixbuf(thumbfile, filename, force_update)
				if pix:
					if self.thumbnail_size != 128:
						# 128 is the size of the saved thumbnail, so convert if different:
						pix, image_width, image_height = self.get_pixbuf_of_size(pix, self.thumbnail_size, gtk.gdk.INTERP_TILES)
					self.thumbnail_loaded[imgnum] = True
					self.thumbscroll.get_vscrollbar().handler_block(self.thumb_scroll_handler)
					pix = self.pixbuf_add_border(pix)
					try:
						self.thumblist[imgnum] = [pix]
					except:
						pass
					self.thumbscroll.get_vscrollbar().handler_unblock(self.thumb_scroll_handler)
	
	def thumbnail_get_name(self, image_name):
		filename = os.path.expanduser('file://' + image_name)
		uriname = os.path.expanduser('file://' + urllib.pathname2url(image_name))
		if HAS_HASHLIB:
		    m = hashlib.md5()
		else:
		    m = md5.new()
		m.update(uriname)
		mhex = m.hexdigest()
		mhex_filename = os.path.expanduser('~/.thumbnails/normal/' + mhex + '.png')
		return filename, mhex_filename
		
	def thumbpane_get_pixbuf(self, thumb_url, image_url, force_generation):
		# Returns a valid pixbuf or None if a pixbuf cannot be generated. Tries to re-use
		# a thumbnail from ~/.thumbails/normal/, otherwise generates one with the
		# XDG filename: md5(file:///full/path/to/image).png
		imgfile = image_url
		if imgfile[:7] == 'file://':
			imgfile = imgfile[7:]
		try:
			if os.path.exists(thumb_url) and not force_generation:
				pix = gtk.gdk.pixbuf_new_from_file(thumb_url)
				pix_mtime = pix.get_option('tEXt::Thumb::MTime')
				if pix_mtime:
					st = os.stat(imgfile)
					file_mtime = str(st[stat.ST_MTIME])
					# If the mtimes match, we're good. if not, regenerate the thumbnail..
					if pix_mtime == file_mtime:
						return pix
			# Create the 128x128 thumbnail:
			uri = 'file://' + urllib.pathname2url(imgfile)
			pix = gtk.gdk.pixbuf_new_from_file(imgfile)
			pix, image_width, image_height = self.get_pixbuf_of_size(pix, 128, gtk.gdk.INTERP_TILES)
			st = os.stat(imgfile)
			file_mtime = str(st[stat.ST_MTIME])
			# Save image to .thumbnails:
			pix.save(thumb_url, "png", {'tEXt::Thumb::URI':uri, 'tEXt::Thumb::MTime':file_mtime, 'tEXt::Software':'Mirage' + __version__})
			return pix
		except:
			return None
	
	def thumbpane_load_image(self, treeview, imgnum):
		if imgnum != self.curr_img_in_list:
			gobject.idle_add(self.goto_image, str(imgnum), None)
		
	def thumbpane_selection_changed(self, treeview):
		cancel = self.autosave_image()
		if cancel:
			# Revert selection...
			gobject.idle_add(self.thumbpane_select, self.curr_img_in_list)
			return True
		try:
			model, paths = self.thumbpane.get_selection().get_selected_rows()
			imgnum = paths[0][0]
			if not self.thumbnail_loaded[imgnum]:
				self.thumbpane_set_image(self.image_list[imgnum], imgnum)
			gobject.idle_add(self.thumbpane_load_image, treeview, imgnum)
		except:
			pass
		
	def thumbpane_select(self, imgnum):
		if self.thumbpane_show:
			self.thumbpane.get_selection().handler_block(self.thumb_sel_handler)
			try:
				self.thumbpane.get_selection().select_path((imgnum,))
				self.thumbpane.scroll_to_cell((imgnum,))
			except:
				pass
			self.thumbpane.get_selection().handler_unblock(self.thumb_sel_handler)

	def thumbpane_set_size(self):
		self.thumbcolumn.set_fixed_width(self.thumbpane_get_size())
		self.window_resized(None, self.window.allocation, True)
	
	def thumbpane_get_size(self):
		return int(self.thumbnail_size * 1.3)
	
	def thumbpane_scrolled(self, range):
		self.thumbpane_update_images()

	def get_blank_pix_for_image(self, image):
		# Sizes the "blank image" icon for the thumbpane. This will ensure that we don't
		# load a humongous icon for a small pix, for example, and will keep the thumbnails
		# from shifting around when they are actually loaded.
		try:
			info = gtk.gdk.pixbuf_get_file_info(image)
			imgwidth = float(info[1])
			imgheight = float(info[2])
			if imgheight > self.thumbnail_size:
				if imgheight > imgwidth:
					imgheight = self.thumbnail_size
				else:
					imgheight = imgheight/imgwidth * self.thumbnail_size
			imgheight = 2 + int(imgheight) # Account for border that will be added to thumbnails..
			imgwidth = self.thumbnail_size
		except:
			imgheight = 2 + self.thumbnail_size
			imgwidth = self.thumbnail_size
		blank_pix = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, True, 8, imgwidth, imgheight)
		blank_pix.fill(0x00000000)
		imgwidth2 = int(imgheight*0.8)
		imgheight2 = int(imgheight*0.8)
		composite_pix = self.blank_image.scale_simple(imgwidth2, imgheight2, gtk.gdk.INTERP_BILINEAR)
		leftcoord = int((imgwidth - imgwidth2)/2)
		topcoord = int((imgheight - imgheight2)/2)
		composite_pix.copy_area(0, 0, imgwidth2, imgheight2, blank_pix, leftcoord, topcoord)
		return blank_pix

	def find_path(self, filename, exit_on_fail=True):
		""" Find a pixmap or icon by looking through standard dirs.
			If the image isn't found exit with error status 1 unless
			exit_on_fail is set to False, then return None """
		if not self.resource_path_list:
			#If executed from mirage in bin this points to the basedir
			basedir_mirage = os.path.split(sys.path[0])[0]
			#If executed from mirage.py module in python lib this points to the basedir
			f0 = os.path.split(__file__)[0].split('/lib')[0]
			self.resource_path_list = list(set(filter(os.path.isdir, [
				os.path.join(basedir_mirage, 'share', 'mirage'),
				os.path.join(basedir_mirage, 'share', 'pixmaps'),
				os.path.join(sys.prefix, 'share', 'mirage'),
				os.path.join(sys.prefix, 'share', 'pixmaps'),
				os.path.join(sys.prefix, 'local', 'share', 'mirage'),
				os.path.join(sys.prefix, 'local', 'share', 'pixmaps'),
				sys.path[0], #If it's run non-installed
				os.path.join(f0, 'share', 'mirage'),
				os.path.join(f0, 'share', 'pixmaps'),
				])))
		for path in self.resource_path_list:
			pix = os.path.join(path, filename)
			if os.path.exists(pix):
				return pix
		# If we reached here, we didn't find the pixmap
		if exit_on_fail:
			print _("Couldn't find the image %s. Please check your installation.") % filename
			sys.exit(1)
		else:
			return None

	def gconf_key_changed(self, client, cnxn_id, entry, label):
		if entry.value.type == gconf.VALUE_STRING:
			style = entry.value.to_string()
			if style == "both":
				self.toolbar.set_style(gtk.TOOLBAR_BOTH)
			elif style == "both-horiz":
				self.toolbar.set_style(gtk.TOOLBAR_BOTH_HORIZ)
			elif style == "icons":
				self.toolbar.set_style(gtk.TOOLBAR_ICONS)
			elif style == "text":
				self.toolbar.set_style(gtk.TOOLBAR_TEXT)
			if self.image_loaded and self.last_image_action_was_fit:
				if self.last_image_action_was_smart_fit:
					self.zoom_to_fit_or_1_to_1(None, False, False)
				else:
					self.zoom_to_fit_window(None, False, False)
	
	def toolbar_focused(self, widget, direction):
		self.layout.grab_focus()
		return True

	def topwindow_keypress(self, widget, event):
		# For whatever reason, 'Left' and 'Right' cannot be used as menu
		# accelerators so we will manually check for them here:
		if event.state != gtk.gdk.SHIFT_MASK and event.state != gtk.gdk.CONTROL_MASK and event.state != gtk.gdk.MOD1_MASK and event.state != gtk.gdk.CONTROL_MASK | gtk.gdk.MOD2_MASK and event.state != gtk.gdk.LOCK_MASK | gtk.gdk.CONTROL_MASK:
			if event.keyval == gtk.gdk.keyval_from_name('Left') or event.keyval == gtk.gdk.keyval_from_name('Up'):
				self.goto_prev_image(None)
				return
			elif event.keyval == gtk.gdk.keyval_from_name('Right') or event.keyval == gtk.gdk.keyval_from_name('Down'):
				self.goto_next_image(None)
				return
		shortcut = gtk.accelerator_name(event.keyval, event.state)
		if "Escape" in shortcut:
			self.stop_now = True
			self.searching_for_images = False
			while gtk.events_pending():
				gtk.main_iteration()
			self.update_title()
			return

	def parse_action_command(self, command, batchmode):
		self.running_custom_actions = True
		self.change_cursor(gtk.gdk.Cursor(gtk.gdk.WATCH))
		while gtk.events_pending():
			gtk.main_iteration()
		self.curr_custom_action = 0
		if batchmode:
			self.num_custom_actions = len(self.image_list)
			for i in range(self.num_custom_actions):
				self.curr_custom_action += 1
				self.update_statusbar()
				while gtk.events_pending():
					gtk.main_iteration()
				imagename = self.image_list[i]
				self.parse_action_command2(command, imagename)
		else:
			self.num_custom_actions = 1
			self.curr_custom_action = 1
			self.update_statusbar()
			while gtk.events_pending():
				gtk.main_iteration()
			self.parse_action_command2(command, self.currimg_name)
		gc.collect()
		self.change_cursor(None)
		# Refresh the current image or any preloaded needed if they have changed:
		if not os.path.exists(self.currimg_name):
			self.currimg_pixbuf_original = None
			self.image_load_failed(False)
		else:
			animtest = gtk.gdk.PixbufAnimation(self.currimg_name)
			if animtest.is_static_image():
				if self.images_are_different(animtest.get_static_image(), self.currimg_pixbuf_original):
					self.load_new_image2(False, False, True, False)
			else:
				if self.images_are_different(animtest, self.currimg_pixbuf_original):
					self.load_new_image2(False, False, True, False)
		self.running_custom_actions = False
		self.update_statusbar()
		while gtk.events_pending():
			gtk.main_iteration()
		if not os.path.exists(self.preloadimg_prev_name):
			self.preloadimg_prev_in_list = -1
		else:
			animtest = gtk.gdk.PixbufAnimation(self.preloadimg_prev_name)
			if animtest.is_static_image():
				if self.images_are_different(animtest.get_static_image(), self.preloadimg_prev_pixbuf_original):
					self.preloadimg_prev_in_list = -1
					self.preload_when_idle = gobject.idle_add(self.preload_prev_image, False)
			else:
				if self.images_are_different(animtest, self.preloadimg_prev_pixbuf_original):
					self.preloadimg_prev_in_list = -1
					self.preload_when_idle = gobject.idle_add(self.preload_prev_image, False)
		if not os.path.exists(self.preloadimg_next_name):
			self.preloadimg_next_in_list = -1
		else:
			animtest = gtk.gdk.PixbufAnimation(self.preloadimg_next_name)
			if animtest.is_static_image():
				if self.images_are_different(animtest.get_static_image(), self.preloadimg_next_pixbuf_original):
					self.preloadimg_next_in_list = -1
					self.preload_when_idle = gobject.idle_add(self.preload_next_image, False)
			else:
				if self.images_are_different(animtest, self.preloadimg_next_pixbuf_original):
					self.preloadimg_next_in_list = -1
					self.preload_when_idle = gobject.idle_add(self.preload_next_image, False)
		self.stop_now = False
		if batchmode:
			# Update all thumbnails:
			gobject.idle_add(self.thumbpane_update_images, True, self.curr_img_in_list)
		else:
			# Update only the current thumbnail:
			gobject.idle_add(self.thumbpane_set_image, self.image_list[self.curr_img_in_list], self.curr_img_in_list, True)

	def images_are_different(self, pixbuf1, pixbuf2):
		if pixbuf1.get_pixels() == pixbuf2.get_pixels():
			return False
		else:
			return True

	def recent_action_click(self, action):
		self.stop_now = True
		while gtk.events_pending():
			gtk.main_iteration()
		cancel = self.autosave_image()
		if cancel:
			return
		index = int(action.get_name())
		if os.path.isfile(self.recentfiles[index]) or os.path.exists(self.recentfiles[index]) or self.recentfiles[index].startswith('http://') or self.recentfiles[index].startswith('ftp://'):
			self.expand_filelist_and_load_image([self.recentfiles[index]])
		else:
			self.image_list = []
			self.curr_img_in_list = 0
			self.image_list.append(self.recentfiles[index])
			self.image_load_failed(False)
			self.recent_file_remove_and_refresh(index)
	
	def recent_file_remove_and_refresh_name(self, rmfile):
		index_num = 0
		for imgfile in self.recentfiles:
			if imgfile == rmfile:
				self.recent_file_remove_and_refresh(index_num)
				break
			index_num += index_num
	
	def recent_file_remove_and_refresh(self, index_num):
		i = index_num
		while i < len(self.recentfiles)-1:
			self.recentfiles[i] = self.recentfiles[i+1]
			i = i + 1
		# Set last item empty:
		self.recentfiles[len(self.recentfiles)-1] = ''
		self.refresh_recent_files_menu()

	def recent_file_add_and_refresh(self, addfile):
		# First check if the filename is already in the list:
		for i in range(len(self.recentfiles)):
			if len(self.recentfiles[i]) > 0:
				if addfile == self.recentfiles[i]:
					# If found in list, put to position 1 and decrement the rest:
					j = i
					while j > 0:
						self.recentfiles[j] = self.recentfiles[j-1]
						j = j - 1
					self.recentfiles[0] = addfile
					self.refresh_recent_files_menu()
					return
		# If not found, put to position 1, decrement the rest:
		j = len(self.recentfiles)-1
		while j > 0:
			self.recentfiles[j] = self.recentfiles[j-1]
			j = j - 1
		if len(self.recentfiles) > 0:
			self.recentfiles[0] = addfile
			self.refresh_recent_files_menu()

	def custom_action_click(self, action):
		if self.UIManager.get_widget('/MainMenu/EditMenu/ActionSubMenu/' + action.get_name()).get_property('sensitive'):
			for i in range(len(self.action_shortcuts)):
				try:
					if action.get_name() == self.action_names[i]:
						self.parse_action_command(self.action_commands[i], self.action_batch[i])
				except:
					pass


	def parse_action_command2(self, cmd, imagename):
		# Executes the given command using ``os.system``, substituting "%"-macros approprately.
		def sh_esc(s):
			import re
			return re.sub(r'[^/._a-zA-Z0-9-]', lambda c: '\\'+c.group(), s)
		cmd = cmd.strip()
		# [NEXT] and [PREV] are only valid alone or at the end of the command
		if cmd == "[NEXT]":
			self.goto_next_image(None)
			return
		elif cmd == "[PREV]":
			self.goto_prev_image(None)
			return
		# -1=go to previous, 1=go to next, 0=don't change
		prev_or_next=0
		if cmd[-6:] == "[NEXT]":
			prev_or_next=1
			cmd = cmd[:-6]
		elif cmd[-6:] == "[PREV]":
			prev_or_next=-1
			cmd = cmd[:-6]
		if "%F" in cmd:
			cmd = cmd.replace("%F", sh_esc(imagename))
		if "%N" in cmd:
			cmd = cmd.replace("%N", sh_esc(os.path.splitext(os.path.basename(imagename))[0]))
		if "%P" in cmd:
			cmd = cmd.replace("%P", sh_esc(os.path.dirname(imagename) + "/"))
		if "%E" in cmd:
			cmd = cmd.replace("%E", sh_esc(os.path.splitext(os.path.basename(imagename))[1]))
		if "%L" in cmd:
			cmd = cmd.replace("%L", " ".join([sh_esc(s) for s in self.image_list]))
		if self.verbose:
			print _("Action: %s") % cmd
		shell_rc = os.system(cmd) >> 8
		if self.verbose:
			print _("Action return code: %s") % shell_rc
		if shell_rc != 0:
			msg = _('Unable to launch \"%s\". Please specify a valid command from Edit > Custom Actions.') % cmd
			error_dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, msg)
			error_dialog.set_title(_("Invalid Custom Action"))
			error_dialog.run()
			error_dialog.destroy()
		elif prev_or_next == 1:
			self.goto_next_image(None)
		elif prev_or_next == -1:
			self.goto_prev_image(None)
		self.running_custom_actions = False

	def set_go_sensitivities(self, enable):
		self.UIManager.get_widget('/MainMenu/GoMenu/Previous Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/GoMenu/Next Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/GoMenu/Random Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/GoMenu/First Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/GoMenu/Last Image').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/Previous Image').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/Next Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainToolbar/Previous2').set_sensitive(enable)
		self.UIManager.get_widget('/MainToolbar/Next2').set_sensitive(enable)
		self.ss_forward.set_sensitive(enable)
		self.ss_back.set_sensitive(enable)

	def set_image_sensitivities(self, enable):
		self.set_zoom_in_sensitivities(enable)
		self.set_zoom_out_sensitivities(enable)
		self.UIManager.get_widget('/MainMenu/ViewMenu/1:1').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/ViewMenu/Fit').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Delete Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Rename Image').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Crop').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Resize').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Saturation').set_sensitive(enable)
		self.UIManager.get_widget('/MainToolbar/1:1').set_sensitive(enable)
		self.UIManager.get_widget('/MainToolbar/Fit').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/1:1').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/Fit').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/FileMenu/Save As').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_sensitive(False)
		self.UIManager.get_widget('/MainMenu/FileMenu/Properties').set_sensitive(False)
		# Only jpeg, png, and bmp images are currently supported for saving
		if len(self.image_list) > 0:
			try:
				filetype = gtk.gdk.pixbuf_get_file_info(self.currimg_name)[0]['name']
				self.UIManager.get_widget('/MainMenu/FileMenu/Properties').set_sensitive(True)
				if self.filetype_is_writable(filetype):
					self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_sensitive(enable)
			except:
				self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_sensitive(False)
		if self.actionGroupCustom:
			for action in self.action_names:
				self.UIManager.get_widget('/MainMenu/EditMenu/ActionSubMenu/' + action).set_sensitive(enable)
		if not HAS_IMGFUNCS:
			enable = False
		self.UIManager.get_widget('/MainMenu/EditMenu/Rotate Left').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Rotate Right').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Flip Vertically').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/EditMenu/Flip Horizontally').set_sensitive(enable)

	def set_zoom_in_sensitivities(self, enable):
		self.UIManager.get_widget('/MainMenu/ViewMenu/In').set_sensitive(enable)
		self.UIManager.get_widget('/MainToolbar/In').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/In').set_sensitive(enable)

	def set_zoom_out_sensitivities(self, enable):
		self.UIManager.get_widget('/MainMenu/ViewMenu/Out').set_sensitive(enable)
		self.UIManager.get_widget('/MainToolbar/Out').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/Out').set_sensitive(enable)

	def set_next_image_sensitivities(self, enable):
		self.UIManager.get_widget('/MainToolbar/Next2').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/GoMenu/Next Image').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/Next Image').set_sensitive(enable)
		self.ss_forward.set_sensitive(enable)

	def set_previous_image_sensitivities(self, enable):
		self.UIManager.get_widget('/MainToolbar/Previous2').set_sensitive(enable)
		self.UIManager.get_widget('/MainMenu/GoMenu/Previous Image').set_sensitive(enable)
		self.UIManager.get_widget('/Popup/Previous Image').set_sensitive(enable)
		self.ss_back.set_sensitive(enable)

	def set_first_image_sensitivities(self, enable):
		self.UIManager.get_widget('/MainMenu/GoMenu/First Image').set_sensitive(enable)

	def set_last_image_sensitivities(self, enable):
		self.UIManager.get_widget('/MainMenu/GoMenu/Last Image').set_sensitive(enable)

	def set_random_image_sensitivities(self, enable):
		self.UIManager.get_widget('/MainMenu/GoMenu/Random Image').set_sensitive(enable)

	def set_slideshow_sensitivities(self):
		if len(self.image_list) <=1:
			self.UIManager.get_widget('/MainMenu/GoMenu/Start Slideshow').show()
			self.UIManager.get_widget('/MainMenu/GoMenu/Start Slideshow').set_sensitive(False)
			self.UIManager.get_widget('/MainMenu/GoMenu/Stop Slideshow').hide()
			self.UIManager.get_widget('/MainMenu/GoMenu/Stop Slideshow').set_sensitive(False)
		elif self.slideshow_mode:
			self.UIManager.get_widget('/MainMenu/GoMenu/Start Slideshow').hide()
			self.UIManager.get_widget('/MainMenu/GoMenu/Start Slideshow').set_sensitive(False)
			self.UIManager.get_widget('/MainMenu/GoMenu/Stop Slideshow').show()
			self.UIManager.get_widget('/MainMenu/GoMenu/Stop Slideshow').set_sensitive(True)
		else:
			self.UIManager.get_widget('/MainMenu/GoMenu/Start Slideshow').show()
			self.UIManager.get_widget('/MainMenu/GoMenu/Start Slideshow').set_sensitive(True)
			self.UIManager.get_widget('/MainMenu/GoMenu/Stop Slideshow').hide()
			self.UIManager.get_widget('/MainMenu/GoMenu/Stop Slideshow').set_sensitive(False)
		if self.slideshow_mode:
			self.UIManager.get_widget('/Popup/Start Slideshow').hide()
			self.UIManager.get_widget('/Popup/Stop Slideshow').show()
		else:
			self.UIManager.get_widget('/Popup/Start Slideshow').show()
			self.UIManager.get_widget('/Popup/Stop Slideshow').hide()
		if len(self.image_list) <=1:
			self.UIManager.get_widget('/Popup/Start Slideshow').set_sensitive(False)
		else:
			self.UIManager.get_widget('/Popup/Start Slideshow').set_sensitive(True)

	def set_zoom_sensitivities(self):
		if not self.currimg_is_animation:
			self.set_zoom_out_sensitivities(True)
			self.set_zoom_in_sensitivities(True)
		else:
			self.set_zoom_out_sensitivities(False)
			self.set_zoom_in_sensitivities(False)

	def print_version(self):
		print _("Version: Mirage"), __version__
		print _("Website: http://mirageiv.berlios.de")

	def print_usage(self):
		self.print_version()
		print ""
		print _("Usage: mirage [OPTION]... FILES|FOLDERS...")
		print ""
		print _("Options") + ":"
		print "  -h, --help           " + _("Show this help and exit")
		print "  -v, --version        " + _("Show version information and exit")
		print "  -V, --verbose        " + _("Show more detailed information")
		print "  -R, --recursive      " + _("Recursively include all images found in")
		print "                       " + _("subdirectories of FOLDERS")
		print "  -s, --slideshow      " + _("Start in slideshow mode")
		print "  -f, --fullscreen     " + _("Start in fullscreen mode")
		print "  -o, --onload 'cmd'   " + _("Execute 'cmd' when an image is loaded")
		print "                       " + _("uses same syntax as custom actions,\n")
		print "                       " + _("i.e. mirage -o 'echo file is %F'")

	def delay_changed(self, action):
		self.curr_slideshow_delay = self.ss_delayspin.get_value()
		if self.slideshow_mode:
			gobject.source_remove(self.timer_delay)
			if self.curr_slideshow_random:
				self.timer_delay = gobject.timeout_add(int(self.curr_slideshow_delay*1000), self.goto_random_image, "ss")
			else:
				self.timer_delay = gobject.timeout_add((self.curr_slideshow_delay*1000), self.goto_next_image, "ss")
		self.window.set_focus(self.layout)

	def random_changed(self, action):
		self.curr_slideshow_random = self.ss_randomize.get_active()

	def motion_cb(self, widget, context, x, y, time):
		context.drag_status(gtk.gdk.ACTION_COPY, time)
		return True

	def drop_cb(self, widget, context, x, y, selection, info, time):
		uri = selection.data.strip()
		path = urllib.url2pathname(uri)
		paths = path.rsplit('\n')
		for i, path in enumerate(paths):
			paths[i] = path.rstrip('\r')
		self.expand_filelist_and_load_image(paths)

	def put_error_image_to_window(self):
		self.imageview.set_from_stock(gtk.STOCK_MISSING_IMAGE, gtk.ICON_SIZE_LARGE_TOOLBAR)
		self.currimg_width = self.imageview.size_request()[0]
		self.currimg_height = self.imageview.size_request()[1]
		self.center_image()
		self.set_go_sensitivities(False)
		self.set_image_sensitivities(False)
		self.update_statusbar()
		self.loaded_img_in_list = -1
		return

	def expose_event(self, widget, event):
		if self.updating_adjustments:
			return
		self.updating_adjustments = True
		if self.hscroll.get_property('visible'):
			try:
				zoomratio = float(self.currimg_width)/self.previmg_width
				newvalue = abs(self.layout.get_hadjustment().get_value() * zoomratio + (self.available_image_width()) * (zoomratio - 1) / 2)
				if newvalue >= self.layout.get_hadjustment().lower and newvalue <= (self.layout.get_hadjustment().upper - self.layout.get_hadjustment().page_size):
					self.layout.get_hadjustment().set_value(newvalue)
			except:
				pass
		if self.vscroll.get_property('visible'):
			try:
				newvalue = abs(self.layout.get_vadjustment().get_value() * zoomratio + (self.available_image_height()) * (zoomratio - 1) / 2)
				if newvalue >= self.layout.get_vadjustment().lower and newvalue <= (self.layout.get_vadjustment().upper - self.layout.get_vadjustment().page_size):
					self.layout.get_vadjustment().set_value(newvalue)
				self.previmg_width = self.currimg_width
			except:
				pass
		self.updating_adjustments = False

	def window_resized(self, widget, allocation, force_update=False):
		# Update the image size on window resize if the current image was last fit:
		if self.image_loaded:
			if force_update or allocation.width != self.prevwinwidth or allocation.height != self.prevwinheight:
				if self.last_image_action_was_fit:
					if self.last_image_action_was_smart_fit:
						self.zoom_to_fit_or_1_to_1(None, False, False)
					else:
						self.zoom_to_fit_window(None, False, False)
				else:
					self.center_image()
				self.load_new_image_stop_now()
				self.show_scrollbars_if_needed()
				# Also, regenerate preloaded image for new window size:
				self.preload_when_idle = gobject.idle_add(self.preload_next_image, True)
				self.preload_when_idle2 = gobject.idle_add(self.preload_prev_image, True)
		self.prevwinwidth = allocation.width
		self.prevwinheight = allocation.height
		return

	def save_settings(self):
		conf = ConfigParser.ConfigParser()
		conf.add_section('window')
		conf.set('window', 'w', self.window.get_allocation().width)
		conf.set('window', 'h', self.window.get_allocation().height)
		conf.set('window', 'toolbar', self.toolbar_show)
		conf.set('window', 'statusbar', self.statusbar_show)
		conf.set('window', 'thumbpane', self.thumbpane_show)
		conf.add_section('prefs')
		conf.set('prefs', 'simple-bgcolor', self.simple_bgcolor)
		conf.set('prefs', 'bgcolor-red', self.bgcolor.red)
		conf.set('prefs', 'bgcolor-green', self.bgcolor.green)
		conf.set('prefs', 'bgcolor-blue', self.bgcolor.blue)
		conf.set('prefs', 'open_all', self.open_all_images)
		conf.set('prefs', 'hidden', self.open_hidden_files)
		conf.set('prefs', 'use_last_dir', self.use_last_dir)
		conf.set('prefs', 'last_dir', self.last_dir)
		conf.set('prefs', 'fixed_dir', self.fixed_dir)
		conf.set('prefs', 'open_mode', self.open_mode)
		conf.set('prefs', 'last_mode', self.last_mode)
		conf.set('prefs', 'listwrap_mode', self.listwrap_mode)
		conf.set('prefs', 'slideshow_delay', int(self.slideshow_delay))
		conf.set('prefs', 'slideshow_random', self.slideshow_random)
		conf.set('prefs', 'zoomquality', self.zoomvalue)
		conf.set('prefs', 'quality_save', int(self.quality_save))
		conf.set('prefs', 'disable_screensaver', self.disable_screensaver)
		conf.set('prefs', 'slideshow_in_fullscreen', self.slideshow_in_fullscreen)
		conf.set('prefs', 'confirm_delete', self.confirm_delete)
		conf.set('prefs', 'preloading_images', self.preloading_images)
		conf.set('prefs', 'savemode', self.savemode)
		conf.set('prefs', 'start_in_fullscreen', self.start_in_fullscreen)
		conf.set('prefs', 'thumbsize', self.thumbnail_size)
		conf.set('prefs', 'screenshot_delay', self.screenshot_delay)
		conf.add_section('actions')
		conf.set('actions', 'num_actions', len(self.action_names))
		for i in range(len(self.action_names)):
			conf.set('actions', 'names[' + str(i) + ']', self.action_names[i])
			conf.set('actions', 'commands[' + str(i) + ']', self.action_commands[i])
			conf.set('actions', 'shortcuts[' + str(i) + ']', self.action_shortcuts[i])
			conf.set('actions', 'batch[' + str(i) + ']', self.action_batch[i])
		conf.add_section('recent')
		conf.set('recent', 'num_recent', len(self.recentfiles))
		for i in range(len(self.recentfiles)):
			conf.set('recent', 'num[' + str(i) + ']', len(self.recentfiles[i]))
			conf.set('recent', 'urls[' + str(i) + ',0]', self.recentfiles[i])
		if not os.path.exists(self.config_dir):
			os.makedirs(self.config_dir)
		conf.write(file(self.config_dir + '/miragerc', 'w'))

		# Also, save accel_map:
		gtk.accel_map_save(self.config_dir + '/accel_map')

		return

	def delete_event(self, widget, event, data=None):
		cancel = self.autosave_image()
		if cancel:
			return True
		self.stop_now = True
		self.closing_app = True
		self.save_settings()
		sys.exit(0)

	def destroy(self, event, data=None):
		cancel = self.autosave_image()
		if cancel:
			return True
		self.stop_now = True
		self.closing_app = True
		self.save_settings()

	def exit_app(self, action):
		cancel = self.autosave_image()
		if cancel:
			return True
		self.stop_now = True
		self.closing_app = True
		self.save_settings()
		sys.exit(0)

	def put_zoom_image_to_window(self, currimg_preloaded):
		self.window.window.freeze_updates()
		if not currimg_preloaded:
			# Always start with the original image to preserve quality!
			# Calculate image size:
			finalimg_width = int(self.currimg_pixbuf_original.get_width() * self.currimg_zoomratio)
			finalimg_height = int(self.currimg_pixbuf_original.get_height() * self.currimg_zoomratio)
			if not self.currimg_is_animation:
				# Scale image:
				if not self.currimg_pixbuf_original.get_has_alpha():
					self.currimg_pixbuf = self.currimg_pixbuf_original.scale_simple(finalimg_width, finalimg_height, self.zoom_quality)
				else:
					colormap = self.imageview.get_colormap()
					light_grey = colormap.alloc_color('#666666', True, True)
					dark_grey = colormap.alloc_color('#999999', True, True)
					self.currimg_pixbuf = self.currimg_pixbuf_original.composite_color_simple(finalimg_width, finalimg_height, self.zoom_quality, 255, 8, light_grey.pixel, dark_grey.pixel)
			else:
				self.currimg_pixbuf = self.currimg_pixbuf_original
			self.currimg_width, self.currimg_height = finalimg_width, finalimg_height
		self.layout.set_size(self.currimg_width, self.currimg_height)
		self.center_image()
		self.show_scrollbars_if_needed()
		if not self.currimg_is_animation:
			self.imageview.set_from_pixbuf(self.currimg_pixbuf)
			self.previmage_is_animation = False
		else:
			self.imageview.set_from_animation(self.currimg_pixbuf)
			self.previmage_is_animation = True
		# Clean up (free memory) because I'm lazy
		gc.collect()
		self.window.window.thaw_updates()
		self.loaded_img_in_list = self.curr_img_in_list

	def show_scrollbars_if_needed(self):
		if self.currimg_width > self.available_image_width():
			self.hscroll.show()
		else:
			self.hscroll.hide()
		if self.currimg_height > self.available_image_height():
			self.vscroll.show()
		else:
			self.vscroll.hide()

	def center_image(self):
		x_shift = int((self.available_image_width() - self.currimg_width)/2)
		if x_shift < 0:
			x_shift = 0
		y_shift = int((self.available_image_height() - self.currimg_height)/2)
		if y_shift < 0:
			y_shift = 0
		self.layout.move(self.imageview, x_shift, y_shift)

	def available_image_width(self):
		width = self.window.get_size()[0]
		if not self.fullscreen_mode:
			if self.thumbpane_show:
				width -= self.thumbscroll.size_request()[0]
		return width

	def available_image_height(self):
		height = self.window.get_size()[1]
		if not self.fullscreen_mode:
			height -= self.menubar.size_request()[1]
			if self.toolbar_show:
				height -= self.toolbar.size_request()[1]
			if self.statusbar_show:
				height -= self.statusbar.size_request()[1]
		return height

	def save_image(self, action):
		if self.UIManager.get_widget('/MainMenu/FileMenu/Save').get_property('sensitive'):
			self.save_image_now(self.currimg_name, gtk.gdk.pixbuf_get_file_info(self.currimg_name)[0]['name'])

	def save_image_as(self, action):
		dialog = gtk.FileChooserDialog(title=_("Save As"),action=gtk.FILE_CHOOSER_ACTION_SAVE,buttons=(gtk.STOCK_CANCEL,gtk.RESPONSE_CANCEL,gtk.STOCK_SAVE,gtk.RESPONSE_OK))
		dialog.set_default_response(gtk.RESPONSE_OK)
		filename = os.path.basename(self.currimg_name)
		filetype = None
		dialog.set_current_folder(os.path.dirname(self.currimg_name))
		dialog.set_current_name(filename)
		dialog.set_do_overwrite_confirmation(True)
		response = dialog.run()
		if response == gtk.RESPONSE_OK:
			prev_name = self.currimg_name
			filename = dialog.get_filename()
			dialog.destroy()
			fileext = os.path.splitext(os.path.basename(filename))[1].lower()
			if len(fileext) > 0:
				fileext = fileext[1:]
			# Override filetype if user typed a filename with a different extension:
			for i in gtk.gdk.pixbuf_get_formats():
				if fileext in i['extensions']:
					filetype = i['name']
			self.save_image_now(filename, filetype)
			self.register_file_with_recent_docs(filename)
		else:
			dialog.destroy()
			
	def save_image_now(self, dest_name, filetype):
		try:
			self.change_cursor(gtk.gdk.Cursor(gtk.gdk.WATCH))
			while gtk.events_pending():
				gtk.main_iteration()
			if filetype == None:
				filetype = gtk.gdk.pixbuf_get_file_info(self.currimg_name)[0]['name']
			if self.filetype_is_writable(filetype):
				self.currimg_pixbuf_original.save(dest_name, filetype, {'quality': str(self.quality_save)})
				self.currimg_name = dest_name
				self.image_list[self.curr_img_in_list] = dest_name
				self.update_title()
				self.update_statusbar()
				# Update thumbnail:
				gobject.idle_add(self.thumbpane_set_image, dest_name, self.curr_img_in_list, True)
				self.image_modified = False
			else:
				error_dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_YES_NO, _('The %s format is not supported for saving. Do you wish to save the file in a different format?') % filetype)
				error_dialog.set_title(_("Save"))
				response = error_dialog.run()
				if response == gtk.RESPONSE_YES:
					error_dialog.destroy()
					while gtk.events_pending():
						gtk.main_iteration()
					self.save_image_as(None)
				else:
					error_dialog.destroy()
		except:
			error_dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, _('Unable to save %s') % dest_name)
			error_dialog.set_title(_("Save"))
			error_dialog.run()
			error_dialog.destroy()
		self.change_cursor(None)

	def autosave_image(self):
		# Returns True if the user has canceled out of the dialog
		# Never call this function from an idle or timeout loop! That will cause
		# the app to freeze.
		if self.image_modified:
			if self.savemode == 1:
				temp = self.UIManager.get_widget('/MainMenu/FileMenu/Save').get_property('sensitive')
				self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_property('sensitive', True)
				self.save_image(None)
				self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_property('sensitive', temp)
			elif self.savemode == 2:
				dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT, gtk.MESSAGE_QUESTION, gtk.BUTTONS_NONE, _("The current image has been modified. Save changes?"))
				dialog.add_button(gtk.STOCK_CANCEL, gtk.RESPONSE_CANCEL)
				dialog.add_button(gtk.STOCK_NO, gtk.RESPONSE_NO)
				dialog.add_button(gtk.STOCK_SAVE, gtk.RESPONSE_YES)
				dialog.set_title(_("Save?"))
				dialog.set_default_response(gtk.RESPONSE_YES)
				response = dialog.run()
				dialog.destroy()
				if response == gtk.RESPONSE_YES:
					temp = self.UIManager.get_widget('/MainMenu/FileMenu/Save').get_property('sensitive')
					self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_property('sensitive', True)
					self.save_image(None)
					self.UIManager.get_widget('/MainMenu/FileMenu/Save').set_property('sensitive', temp)
					self.image_modified = False
				elif response == gtk.RESPONSE_NO:
					self.image_modified = False
					# Ensures that we don't use the current pixbuf for any preload pixbufs if we are in
					# the process of loading the previous or next image in the list:
					self.currimg_pixbuf = self.currimg_pixbuf_original
					self.preloadimg_next_in_list = -1
					self.preloadimg_prev_in_list = -1
					self.loaded_img_in_list = -1
				else:
					return True

	def filetype_is_writable(self, filetype):
		# Determine if filetype is a writable format
		filetype_is_writable = True
		for i in gtk.gdk.pixbuf_get_formats():
			if filetype in i['extensions']:
				if i['is_writable']:
					return True
		return False

	def open_file(self, action):
		self.stop_now = True
		while gtk.events_pending():
			gtk.main_iteration()
		self.open_file_or_folder(action, True)
	
	def open_file_remote(self, action):
		# Prompt user for the url:
		dialog = gtk.Dialog(_("Open Remote"), self.window, gtk.DIALOG_MODAL, buttons=(gtk.STOCK_CANCEL,gtk.RESPONSE_CANCEL,gtk.STOCK_OPEN,gtk.RESPONSE_OK))
		location = gtk.Entry()
		location.set_size_request(300, -1)
		location.set_activates_default(True)
		hbox = gtk.HBox()
		hbox.pack_start(gtk.Label(_("Image Location (URL):")), False, False, 5)
		hbox.pack_start(location, True, True, 5)
		dialog.vbox.pack_start(hbox, True, True, 10)
		dialog.set_default_response(gtk.RESPONSE_OK)
		dialog.vbox.show_all()
		dialog.connect('response', self.open_file_remote_response,  location)
		response = dialog.show()
	
	def open_file_remote_response(self, dialog, response, location):
		if response == gtk.RESPONSE_OK:
			filenames = []
			filenames.append(location.get_text())
			dialog.destroy()
			while gtk.events_pending():
				gtk.main_iteration()
			self.expand_filelist_and_load_image(filenames)
		else:
			dialog.destroy()

	def open_folder(self, action):
		self.stop_now = True
		while gtk.events_pending():
			gtk.main_iteration()
		self.open_file_or_folder(action, False)

	def open_file_or_folder(self, action, isfile):
		self.thumbpane_create_dir()
		cancel = self.autosave_image()
		if cancel:
			return
		# If isfile = True, file; If isfile = False, folder
		dialog = gtk.FileChooserDialog(title=_("Open"),action=gtk.FILE_CHOOSER_ACTION_OPEN,buttons=(gtk.STOCK_CANCEL,gtk.RESPONSE_CANCEL,gtk.STOCK_OPEN,gtk.RESPONSE_OK))
		if isfile:
			filter = gtk.FileFilter()
			filter.set_name(_("Images"))
			filter.add_pixbuf_formats()
			dialog.add_filter(filter)
			filter = gtk.FileFilter()
			filter.set_name(_("All files"))
			filter.add_pattern("*")
			dialog.add_filter(filter)
			preview = gtk.Image()
			dialog.set_preview_widget(preview)
			dialog.set_use_preview_label(False)
			dialog.connect("update-preview", self.update_preview, preview)
			recursivebutton = None
		else:
			dialog.set_action(gtk.FILE_CHOOSER_ACTION_SELECT_FOLDER)
			recursivebutton = gtk.CheckButton(label=_("Include images in subdirectories"))
			dialog.set_extra_widget(recursivebutton)
		dialog.set_default_response(gtk.RESPONSE_OK)
		dialog.set_select_multiple(True)
		if self.use_last_dir:
			if self.last_dir != None:
				dialog.set_current_folder(self.last_dir)
		else:
			if self.fixed_dir != None:
				dialog.set_current_folder(self.fixed_dir)
		dialog.connect("response", self.open_file_or_folder_response, isfile, recursivebutton)
		response = dialog.show()
	
	def open_file_or_folder_response(self, dialog, response, isfile, recursivebutton):
		if response == gtk.RESPONSE_OK:
			if self.use_last_dir:
				self.last_dir = dialog.get_current_folder()
			if not isfile and recursivebutton.get_property('active'):
				self.recursive = True
			filenames = dialog.get_filenames()
			dialog.destroy()
			while gtk.events_pending():
				gtk.main_iteration()
			self.expand_filelist_and_load_image(filenames)
		else:
			dialog.destroy()

	def update_preview(self, file_chooser, preview):
		filename = file_chooser.get_preview_filename()
		if not filename:
			return
		filename, thumbfile = self.thumbnail_get_name(filename)
		pixbuf = self.thumbpane_get_pixbuf(thumbfile, filename, False)
		if pixbuf:
			preview.set_from_pixbuf(pixbuf)
		else:
			pixbuf = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, 1, 8, 128, 128)
			pixbuf.fill(0x00000000)
			preview.set_from_pixbuf(pixbuf)
		have_preview = True
		file_chooser.set_preview_widget_active(have_preview)
		del pixbuf
		gc.collect()

	def hide_cursor(self):
		if self.fullscreen_mode and not self.user_prompt_visible and not self.slideshow_controls_visible:
			pix_data = """/* XPM */
			static char * invisible_xpm[] = {
			"1 1 1 1",
			"       c None",
			" "};"""
			color = gtk.gdk.Color()
			pix = gtk.gdk.pixmap_create_from_data(None, pix_data, 1, 1, 1, color, color)
			invisible = gtk.gdk.Cursor(pix, pix, color, color, 0, 0)
			self.change_cursor(invisible)
		return False

	def enter_fullscreen(self, action):
		if not self.fullscreen_mode:
			self.fullscreen_mode = True
			self.UIManager.get_widget('/Popup/Full Screen').hide()
			self.UIManager.get_widget('/Popup/Exit Full Screen').show()
			self.statusbar.hide()
			self.statusbar2.hide()
			self.toolbar.hide()
			self.menubar.hide()
			self.thumbscroll.hide()
			self.thumbpane.hide()
			self.window.fullscreen()
			self.timer_id = gobject.timeout_add(2000, self.hide_cursor)
			self.set_slideshow_sensitivities()
			if self.simple_bgcolor:
				self.layout.modify_bg(gtk.STATE_NORMAL, self.bgcolor)
		else:
			if self.simple_bgcolor:
				self.layout.modify_bg(gtk.STATE_NORMAL, None)
			self.leave_fullscreen(action)

	def leave_fullscreen(self, action):
		if self.fullscreen_mode:
			self.slideshow_controls_visible = False
			self.slideshow_window.hide_all()
			self.slideshow_window2.hide_all()
			self.fullscreen_mode = False
			self.UIManager.get_widget('/Popup/Full Screen').show()
			self.UIManager.get_widget('/Popup/Exit Full Screen').hide()
			if self.toolbar_show:
				self.toolbar.show()
			self.menubar.show()
			if self.statusbar_show:
				self.statusbar.show()
				self.statusbar2.show()
			if self.thumbpane_show:
				self.thumbscroll.show()
				self.thumbpane.show()
				self.thumbpane_update_images(False, self.curr_img_in_list)
			self.window.unfullscreen()
			self.change_cursor(None)
			self.set_slideshow_sensitivities()
			if self.simple_bgcolor:
				self.layout.modify_bg(gtk.STATE_NORMAL, None)

	def toggle_status_bar(self, action):
		if self.statusbar.get_property('visible'):
			self.statusbar.hide()
			self.statusbar2.hide()
			self.statusbar_show = False
		else:
			self.statusbar.show()
			self.statusbar2.show()
			self.statusbar_show = True
		if self.image_loaded and self.last_image_action_was_fit:
			if self.last_image_action_was_smart_fit:
				self.zoom_to_fit_or_1_to_1(None, False, False)
			else:
				self.zoom_to_fit_window(None, False, False)
				
	def toggle_thumbpane(self, action):
		if self.thumbscroll.get_property('visible'):
			self.thumbscroll.hide()
			self.thumbpane.hide()
			self.thumbpane_show = False
		else:
			self.thumbscroll.show()
			self.thumbpane.show()
			self.thumbpane_show = True
			self.stop_now = False
			gobject.idle_add(self.thumbpane_update_images, True, self.curr_img_in_list)
		if self.image_loaded and self.last_image_action_was_fit:
			if self.last_image_action_was_smart_fit:
				self.zoom_to_fit_or_1_to_1(None, False, False)
			else:
				self.zoom_to_fit_window(None, False, False)

	def toggle_toolbar(self, action):
		if self.toolbar.get_property('visible'):
			self.toolbar.hide()
			self.toolbar_show = False
		else:
			self.toolbar.show()
			self.toolbar_show = True
		if self.image_loaded and self.last_image_action_was_fit:
			if self.last_image_action_was_smart_fit:
				self.zoom_to_fit_or_1_to_1(None, False, False)
			else:
				self.zoom_to_fit_window(None, False, False)

	def update_statusbar(self):
		# Update status bar:
		try:
			st = os.stat(self.currimg_name)
			filesize = st[stat.ST_SIZE]/1000
			ratio = int(100 * self.currimg_zoomratio)
			status_text = os.path.basename(self.currimg_name)+ ":  " +  str(self.currimg_pixbuf_original.get_width()) + "x" + str(self.currimg_pixbuf_original.get_height()) + "   " + str(filesize) + "KB   " + str(ratio) + "%   "
		except:
			status_text=_("Cannot load image.")
		self.statusbar.push(self.statusbar.get_context_id(""), status_text)
		status_text = ""
		if self.running_custom_actions:
			status_text = _('Custom actions: %(current)i of  %(total)i') % {'current': self.curr_custom_action,'total': self.num_custom_actions}
		elif self.searching_for_images:
			status_text = _('Scanning...')
		self.statusbar2.push(self.statusbar2.get_context_id(""), status_text)

	def show_custom_actions(self, action):
		self.actions_dialog = gtk.Dialog(title=_("Configure Custom Actions"), parent=self.window)
		self.actions_dialog.set_has_separator(False)
		self.actions_dialog.set_resizable(False)
		table_actions = gtk.Table(13, 2, False)
		table_actions.attach(gtk.Label(), 1, 2, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		actionscrollwindow = gtk.ScrolledWindow()
		self.actionstore = gtk.ListStore(str, str, str)
		self.actionwidget = gtk.TreeView()
		self.actionwidget.set_enable_search(False)
		self.actionwidget.set_rules_hint(True)
		self.actionwidget.connect('row-activated', self.edit_custom_action2)
		actionscrollwindow.add(self.actionwidget)
		actionscrollwindow.set_shadow_type(gtk.SHADOW_IN)
		actionscrollwindow.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
		actionscrollwindow.set_size_request(500, 200)
		self.actionwidget.set_model(self.actionstore)
		self.cell = gtk.CellRendererText()
		self.cellbool = gtk.CellRendererPixbuf()
		self.tvcolumn0 = gtk.TreeViewColumn(_("Batch"))
		self.tvcolumn1 = gtk.TreeViewColumn(_("Action"), self.cell, markup=0)
		self.tvcolumn2 = gtk.TreeViewColumn(_("Shortcut"))
		self.tvcolumn1.set_max_width(self.actionwidget.size_request()[0] - self.tvcolumn0.get_width() - self.tvcolumn2.get_width())
		self.actionwidget.append_column(self.tvcolumn0)
		self.actionwidget.append_column(self.tvcolumn1)
		self.actionwidget.append_column(self.tvcolumn2)
		self.populate_treeview()
		if len(self.action_names) > 0:
			self.actionwidget.get_selection().select_path(0)
		vbox_actions = gtk.VBox()
		addbutton = gtk.Button("", gtk.STOCK_ADD)
		addbutton.get_child().get_child().get_children()[1].set_text('')
		addbutton.connect('clicked', self.add_custom_action, self.actionwidget)
		addbutton.set_tooltip_text(_("Add action"))
		editbutton = gtk.Button("", gtk.STOCK_EDIT)
		editbutton.get_child().get_child().get_children()[1].set_text('')
		editbutton.connect('clicked', self.edit_custom_action, self.actionwidget)
		editbutton.set_tooltip_text(_("Edit selected action."))
		removebutton = gtk.Button("", gtk.STOCK_REMOVE)
		removebutton.get_child().get_child().get_children()[1].set_text('')
		removebutton.connect('clicked', self.remove_custom_action)
		removebutton.set_tooltip_text(_("Remove selected action."))
		upbutton = gtk.Button("", gtk.STOCK_GO_UP)
		upbutton.get_child().get_child().get_children()[1].set_text('')
		upbutton.connect('clicked', self.custom_action_move_up, self.actionwidget)
		upbutton.set_tooltip_text(_("Move selected action up."))
		downbutton = gtk.Button("", gtk.STOCK_GO_DOWN)
		downbutton.get_child().get_child().get_children()[1].set_text('')
		downbutton.connect('clicked', self.custom_action_move_down, self.actionwidget)
		downbutton.set_tooltip_text(_("Move selected action down."))
		vbox_buttons = gtk.VBox()
		propertyinfo = gtk.Label()
		propertyinfo.set_markup('<small>' + _("Parameters") + ':\n<span font_family="Monospace">%F</span> - ' + _("File path, name, and extension") + '\n<span font_family="Monospace">%P</span> - ' + _("File path") + '\n<span font_family="Monospace">%N</span> - ' + _("File name without file extension") + '\n<span font_family="Monospace">%E</span> - ' + _("File extension (i.e. \".png\")") + '\n<span font_family="Monospace">%L</span> - ' + _("List of files, space-separated") + '</small>')
		propertyinfo.set_alignment(0, 0)
		actioninfo = gtk.Label()
		actioninfo.set_markup('<small>' + _("Operations") + ':\n<span font_family="Monospace">[NEXT]</span> - ' + _("Go to next image") + '\n<span font_family="Monospace">[PREV]</span> - ' + _("Go to previous image") +'</small>')
		actioninfo.set_alignment(0, 0)
		hbox_info = gtk.HBox()
		hbox_info.pack_start(propertyinfo, False, False, 15)
		hbox_info.pack_start(actioninfo, False, False, 15)
		vbox_buttons.pack_start(addbutton, False, False, 5)
		vbox_buttons.pack_start(editbutton, False, False, 5)
		vbox_buttons.pack_start(removebutton, False, False, 5)
		vbox_buttons.pack_start(upbutton, False, False, 5)
		vbox_buttons.pack_start(downbutton, False, False, 0)
		hbox_top = gtk.HBox()
		hbox_top.pack_start(actionscrollwindow, True, True, 5)
		hbox_top.pack_start(vbox_buttons, False, False, 5)
		vbox_actions.pack_start(hbox_top, True, True, 5)
		vbox_actions.pack_start(hbox_info, False, False, 5)
		hbox_instructions = gtk.HBox()
		info_image = gtk.Image()
		info_image.set_from_stock(gtk.STOCK_DIALOG_INFO, gtk.ICON_SIZE_BUTTON)
		hbox_instructions.pack_start(info_image, False, False, 5)
		instructions = gtk.Label(_("Here you can define custom actions with shortcuts. Actions use the built-in parameters and operations listed below and can have multiple statements separated by a semicolon. Batch actions apply to all images in the list."))
		instructions.set_line_wrap(True)
		instructions.set_alignment(0, 0.5)
		hbox_instructions.pack_start(instructions, False, False, 5)
		table_actions.attach(hbox_instructions, 1, 3, 2, 3,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 5, 0)
		table_actions.attach(gtk.Label(), 1, 3, 3, 4,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_actions.attach(vbox_actions, 1, 3, 4, 12, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_actions.attach(gtk.Label(), 1, 3, 12, 13,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		self.actions_dialog.vbox.pack_start(table_actions, False, False, 0)
		# Show dialog:
		self.actions_dialog.vbox.show_all()
		instructions.set_size_request(self.actions_dialog.size_request()[0]-50, -1)
		close_button = self.actions_dialog.add_button(gtk.STOCK_CLOSE, gtk.RESPONSE_CLOSE)
		close_button.grab_focus()
		self.actions_dialog.run()
		self.refresh_custom_actions_menu()
		while gtk.events_pending():
			gtk.main_iteration()
		if len(self.image_list) == 0:
			self.set_image_sensitivities(False)
		self.actions_dialog.destroy()

	def add_custom_action(self, button, treeview):
		self.open_custom_action_dialog(True, '', '', 'None', False, treeview)

	def edit_custom_action2(self, treeview, path, view_column):
		self.edit_custom_action(None, treeview)

	def edit_custom_action(self, button, treeview):
		(model, iter) = self.actionwidget.get_selection().get_selected()
		if iter != None:
			(row, ) = self.actionstore.get_path(iter)
			self.open_custom_action_dialog(False, self.action_names[row], self.action_commands[row], self.action_shortcuts[row], self.action_batch[row], treeview)

	def open_custom_action_dialog(self, add_call, name, command, shortcut, batch, treeview):
		if add_call:
			self.dialog_name = gtk.Dialog(_("Add Custom Action"), self.actions_dialog, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT, gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
		else:
			self.dialog_name = gtk.Dialog(_("Edit Custom Action"), self.actions_dialog, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT, gtk.STOCK_OK, gtk.RESPONSE_ACCEPT))
		self.dialog_name.set_modal(True)
		table = gtk.Table(2, 4, False)
		action_name_label = gtk.Label(_("Action Name:"))
		action_name_label.set_alignment(0, 0.5)
		action_command_label = gtk.Label(_("Command:"))
		action_command_label.set_alignment(0, 0.5)
		shortcut_label = gtk.Label(_("Shortcut:"))
		shortcut_label.set_alignment(0, 0.5)
		table.attach(action_name_label, 0, 1, 0, 1, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table.attach(action_command_label, 0, 1, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table.attach(shortcut_label, 0, 1, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		action_name = gtk.Entry()
		action_name.set_text(name)
		action_command = gtk.Entry()
		action_command.set_text(command)
		table.attach(action_name, 1, 2, 0, 1, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table.attach(action_command, 1, 2, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		self.shortcut = gtk.Button(shortcut)
		self.shortcut.connect('clicked', self.shortcut_clicked)
		table.attach(self.shortcut, 1, 2, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		batchmode = gtk.CheckButton(_("Perform action on all images (Batch)"))
		batchmode.set_active(batch)
		table.attach(batchmode, 0, 2, 3, 4, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		self.dialog_name.vbox.pack_start(table, False, False, 5)
		self.dialog_name.vbox.show_all()
		self.dialog_name.connect('response', self.dialog_name_response, add_call, action_name, action_command, self.shortcut, batchmode, treeview)
		self.dialog_name.run()

	def dialog_name_response(self, dialog, response, add_call, action_name, action_command, shortcut, batchmode, treeview):
		if response == gtk.RESPONSE_ACCEPT:
			if not (action_command.get_text() == "" or action_name.get_text() == "" or self.shortcut.get_label() == "None"):
				name = action_name.get_text()
				command = action_command.get_text()
				if ((("[NEXT]" in command.strip()) and command.strip()[-6:] != "[NEXT]") or (("[PREV]" in command.strip()) and command.strip()[-6:] != "[PREV]") ):
					error_dialog = gtk.MessageDialog(self.actions_dialog, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, _('[PREV] and [NEXT] are only valid alone or at the end of the command'))
					error_dialog.set_title(_("Invalid Custom Action"))
					error_dialog.run()
					error_dialog.destroy()
					return
				shortcut = shortcut.get_label()
				batch = batchmode.get_active()
				dialog.destroy()
				if add_call:
					self.action_names.append(name)
					self.action_commands.append(command)
					self.action_shortcuts.append(shortcut)
					self.action_batch.append(batch)
				else:
					(model, iter) = self.actionwidget.get_selection().get_selected()
					(rownum, ) = self.actionstore.get_path(iter)
					self.action_names[rownum] = name
					self.action_commands[rownum] = command
					self.action_shortcuts[rownum] = shortcut
					self.action_batch[rownum] = batch
				self.populate_treeview()
				if add_call:
					rownum = len(self.action_names)-1
				treeview.get_selection().select_path(rownum)
				while gtk.events_pending():
					gtk.main_iteration()
				# Keep item in visible rect:
				visible_rect = treeview.get_visible_rect()
				row_rect = treeview.get_background_area(rownum, self.tvcolumn1)
				if row_rect.y + row_rect.height > visible_rect.height:
					top_coord = (row_rect.y + row_rect.height - visible_rect.height) + visible_rect.y
					treeview.scroll_to_point(-1, top_coord)
				elif row_rect.y < 0:
					treeview.scroll_to_cell(rownum)
			else:
				error_dialog = gtk.MessageDialog(self.actions_dialog, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, _('Incomplete custom action specified.'))
				error_dialog.set_title(_("Invalid Custom Action"))
				error_dialog.run()
				error_dialog.destroy()
		else:
			dialog.destroy()

	def custom_action_move_down(self, button, treeview):
		iter = None
		selection = treeview.get_selection()
		model, iter = selection.get_selected()
		if iter:
			rownum = int(model.get_string_from_iter(iter))
			if rownum < len(self.action_names)-1:
				# Move item down:
				temp_name = self.action_names[rownum]
				temp_shortcut = self.action_shortcuts[rownum]
				temp_command = self.action_commands[rownum]
				temp_batch = self.action_batch[rownum]
				self.action_names[rownum] = self.action_names[rownum+1]
				self.action_shortcuts[rownum] = self.action_shortcuts[rownum+1]
				self.action_commands[rownum] = self.action_commands[rownum+1]
				self.action_batch[rownum] =  self.action_batch[rownum+1]
				self.action_names[rownum+1] = temp_name
				self.action_shortcuts[rownum+1] = temp_shortcut
				self.action_commands[rownum+1] = temp_command
				self.action_batch[rownum+1] = temp_batch
				# Repopulate treeview and keep item selected:
				self.populate_treeview()
				selection.select_path((rownum+1,))
				while gtk.events_pending():
					gtk.main_iteration()
				# Keep item in visible rect:
				rownum = rownum + 1
				visible_rect = treeview.get_visible_rect()
				row_rect = treeview.get_background_area(rownum, self.tvcolumn1)
				if row_rect.y + row_rect.height > visible_rect.height:
					top_coord = (row_rect.y + row_rect.height - visible_rect.height) + visible_rect.y
					treeview.scroll_to_point(-1, top_coord)
				elif row_rect.y < 0:
					treeview.scroll_to_cell(rownum)

	def custom_action_move_up(self, button, treeview):
		iter = None
		selection = treeview.get_selection()
		model, iter = selection.get_selected()
		if iter:
			rownum = int(model.get_string_from_iter(iter))
			if rownum > 0:
				# Move item down:
				temp_name = self.action_names[rownum]
				temp_shortcut = self.action_shortcuts[rownum]
				temp_command = self.action_commands[rownum]
				temp_batch = self.action_batch[rownum]
				self.action_names[rownum] = self.action_names[rownum-1]
				self.action_shortcuts[rownum] = self.action_shortcuts[rownum-1]
				self.action_commands[rownum] = self.action_commands[rownum-1]
				self.action_batch[rownum] =  self.action_batch[rownum-1]
				self.action_names[rownum-1] = temp_name
				self.action_shortcuts[rownum-1] = temp_shortcut
				self.action_commands[rownum-1] = temp_command
				self.action_batch[rownum-1] = temp_batch
				# Repopulate treeview and keep item selected:
				self.populate_treeview()
				selection.select_path((rownum-1,))
				while gtk.events_pending():
					gtk.main_iteration()
				# Keep item in visible rect:
				rownum = rownum - 1
				visible_rect = treeview.get_visible_rect()
				row_rect = treeview.get_background_area(rownum, self.tvcolumn1)
				if row_rect.y + row_rect.height > visible_rect.height:
					top_coord = (row_rect.y + row_rect.height - visible_rect.height) + visible_rect.y
					treeview.scroll_to_point(-1, top_coord)
				elif row_rect.y < 0:
					treeview.scroll_to_cell(rownum)

	def shortcut_clicked(self, widget):
		self.dialog_shortcut = gtk.Dialog(_("Action Shortcut"), self.dialog_name, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT))
		self.shortcut_label = gtk.Label(_("Press the desired shortcut for the action."))
		hbox = gtk.HBox()
		hbox.pack_start(self.shortcut_label, False, False, 15)
		self.dialog_shortcut.vbox.pack_start(hbox, False, False, 5)
		self.dialog_shortcut.vbox.show_all()
		self.dialog_shortcut.connect('key-press-event', self.shortcut_keypress)
		self.dialog_shortcut.run()
		self.dialog_shortcut.destroy()

	def shortcut_keypress(self, widget, event):
		shortcut = gtk.accelerator_name(event.keyval, event.state)
		if "<Mod2>" in shortcut:
			shortcut = shortcut.replace("<Mod2>", "")
		if shortcut[(len(shortcut)-2):len(shortcut)] != "_L" and shortcut[(len(shortcut)-2):len(shortcut)] != "_R":
			# Validate to make sure the shortcut hasn't already been used:
			for i in range(len(self.keys)):
				if shortcut == self.keys[i][1]:
					error_dialog = gtk.MessageDialog(self.dialog_shortcut, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, _('The shortcut \'%(shortcut)s\' is already used for \'%(key)s\'.') % {'shortcut': shortcut, 'key': self.keys[i][0]})
					error_dialog.set_title(_("Invalid Shortcut"))
					error_dialog.run()
					error_dialog.destroy()
					return
			for i in range(len(self.action_shortcuts)):
				if shortcut == self.action_shortcuts[i]:
					error_dialog = gtk.MessageDialog(self.dialog_shortcut, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, _('The shortcut \'%(shortcut)s\' is already used for \'%(key)s\'.') % {'shortcut': shortcut, 'key': self.action_names[i]})
					error_dialog.set_title(_("Invalid Shortcut"))
					error_dialog.run()
					error_dialog.destroy()
					return
			self.shortcut.set_label(shortcut)
			widget.destroy()

	def remove_custom_action(self, button):
		(model, iter) = self.actionwidget.get_selection().get_selected()
		if iter != None:
			(row, ) = self.actionstore.get_path(iter)
			self.action_names.pop(row)
			self.action_shortcuts.pop(row)
			self.action_commands.pop(row)
			self.action_batch.pop(row)
			self.populate_treeview()
			self.actionwidget.grab_focus()

	def populate_treeview(self):
		self.actionstore.clear()
		for i in range(len(self.action_names)):
			if self.action_batch[i]:
				pb = gtk.STOCK_APPLY
			else:
				pb = None
			self.actionstore.append([pb, '<big><b>' + self.action_names[i].replace('&','&amp;') + '</b></big>\n<small>' + self.action_commands[i].replace('&','&amp;') + '</small>', self.action_shortcuts[i]])
		self.tvcolumn0.clear()
		self.tvcolumn1.clear()
		self.tvcolumn2.clear()
		self.tvcolumn0.pack_start(self.cellbool)
		self.tvcolumn1.pack_start(self.cell)
		self.tvcolumn2.pack_start(self.cell)
		self.tvcolumn0.add_attribute(self.cellbool, "stock-id", 0)
		self.tvcolumn1.set_attributes(self.cell, markup=1)
		self.tvcolumn2.set_attributes(self.cell, text=2)
		self.tvcolumn1.set_expand(True)
	
	def screenshot(self, action):
		cancel = self.autosave_image()
		if cancel:
			return
		# Dialog:
		dialog = gtk.Dialog(_("Screenshot"), self.window, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT))
		snapbutton = dialog.add_button(_("_Snap"), gtk.RESPONSE_ACCEPT)
		snapimage = gtk.Image()
		snapimage.set_from_stock(gtk.STOCK_OK, gtk.ICON_SIZE_BUTTON)
		snapbutton.set_image(snapimage)
		loc = gtk.Label()
		loc.set_markup('<b>' + _('Location') + '</b>')
		loc.set_alignment(0, 0)
		area = gtk.RadioButton()
		area1 = gtk.RadioButton(group=area, label=_("Entire screen"))
		area2 = gtk.RadioButton(group=area, label=_("Window under pointer"))
		if not HAS_XMOUSE:
			area2.set_sensitive(False)
		area1.set_active(True)
		de = gtk.Label()
		de.set_markup('<b>' + _("Delay") + '</b>')
		de.set_alignment(0, 0)
		delaybox = gtk.HBox()
		adj = gtk.Adjustment(self.screenshot_delay, 0, 30, 1, 10, 0)
		delay = gtk.SpinButton(adj, 0, 0)
		delay.set_numeric(True)
		delay.set_update_policy(gtk.UPDATE_IF_VALID)
		delay.set_wrap(False)
		delaylabel = gtk.Label(_(" seconds"))
		delaybox.pack_start(delay, False)
		delaybox.pack_start(delaylabel, False)
		table = gtk.Table()
		table.attach(gtk.Label(), 1, 2, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table.attach(loc, 1, 2, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table.attach(gtk.Label(), 1, 2, 3, 4, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table.attach(area1, 1, 2, 4, 5, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table.attach(area2, 1, 2, 5, 6, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table.attach(gtk.Label(), 1, 2, 6, 7, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table.attach(de, 1, 2, 7, 8,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table.attach(gtk.Label(), 1, 2, 8, 9,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table.attach(delaybox, 1, 2, 9, 10, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table.attach(gtk.Label(), 1, 2, 10, 11,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		dialog.vbox.pack_start(table)
		dialog.set_default_response(gtk.RESPONSE_ACCEPT)
		dialog.vbox.show_all()
		response = dialog.run()
		if response == gtk.RESPONSE_ACCEPT:
			dialog.destroy()
			while gtk.events_pending():
				gtk.main_iteration()
			self.screenshot_delay = int(delay.get_text())
			gobject.timeout_add(int(self.screenshot_delay*1000), self._screenshot_grab, area1.get_active())
		else:
			dialog.destroy()
	
	def _screenshot_grab(self, entire_screen):
		root_win = gtk.gdk.get_default_root_window()
		if entire_screen:
			x = 0
			y = 0
			width = gtk.gdk.screen_width()
			height = gtk.gdk.screen_height()
		else:
			(x, y, width, height) = xmouse.geometry()
		pix = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, True, 8, width, height)
		pix = pix.get_from_drawable(root_win, gtk.gdk.colormap_get_system(), x, y, 0, 0, width, height)
		# Save as /tmp/mirage-<random>/filename.ext
		tmpdir = tempfile.mkdtemp(prefix="mirage-") + "/"
		tmpfile = tmpdir + "screenshot.png"
		pix.save(tmpfile, 'png')
		# Load file:
		self.image_list = [tmpfile]
		self.curr_img_in_list = 0
		gobject.idle_add(self.load_new_image2, False, False, False, False, True)
		self.update_statusbar()
		self.set_go_navigation_sensitivities(False)
		self.set_slideshow_sensitivities()
		self.thumbpane_update_images(True, self.curr_img_in_list)
		del pix
		self.window.present()

	def show_properties(self, action):
		show_props = gtk.Dialog(_("Properties"), self.window)
		show_props.set_has_separator(False)
		show_props.set_resizable(False)
		table = gtk.Table(3, 3, False)
		image = gtk.Image()
		animtest = gtk.gdk.PixbufAnimation(self.currimg_name)
		image_is_anim = False
		if animtest.is_static_image():
			pixbuf, image_width, image_height = self.get_pixbuf_of_size(self.currimg_pixbuf_original, 180, self.zoom_quality)
		else:
			pixbuf, image_width, image_height = self.get_pixbuf_of_size(animtest.get_static_image(), 180, self.zoom_quality)
			image_is_anim = True
		image.set_from_pixbuf(self.pixbuf_add_border(pixbuf))
		vbox_left = gtk.VBox()
		filename = gtk.Label(_("File name:"))
		filename.set_alignment(1, 1)
		filedate = gtk.Label(_("File modified:"))
		filedate.set_alignment(1, 1)
		imagesize = gtk.Label(_("Dimensions:"))
		imagesize.set_alignment(1, 1)
		filesize = gtk.Label(_("File size:"))
		filesize.set_alignment(1, 1)
		filetype = gtk.Label(_("File type:"))
		filetype.set_alignment(1, 1)
		transparency = gtk.Label(_("Transparency:"))
		transparency.set_alignment(1, 1)
		animation = gtk.Label(_("Animation:"))
		animation.set_alignment(1, 1)
		bits = gtk.Label(_("Bits per sample:"))
		bits.set_alignment(1, 1)
		channels = gtk.Label(_("Channels:"))
		channels.set_alignment(1, 1)
		vbox_left.pack_start(filename, False, False, 2)
		vbox_left.pack_start(filedate, False, False, 2)
		vbox_left.pack_start(imagesize, False, False, 2)
		vbox_left.pack_start(filesize, False, False, 2)
		vbox_left.pack_start(filetype, False, False, 2)
		vbox_left.pack_start(transparency, False, False, 2)
		vbox_left.pack_start(animation, False, False, 2)
		vbox_left.pack_start(bits, False, False, 2)
		vbox_left.pack_start(channels, False, False, 2)
		vbox_right = gtk.VBox()
		filestat = os.stat(self.currimg_name)
		filename2 = gtk.Label(os.path.basename(self.currimg_name))
		filedate2 = gtk.Label(time.strftime('%c', time.localtime(filestat[stat.ST_MTIME])))
		imagesize2 = gtk.Label(str(self.currimg_pixbuf_original.get_width()) + "x" + str(self.currimg_pixbuf_original.get_height()))
		filetype2 = gtk.Label(gtk.gdk.pixbuf_get_file_info(self.currimg_name)[0]['mime_types'][0])
		filesize2 = gtk.Label(str(filestat[stat.ST_SIZE]/1000) + "KB")
		if not image_is_anim and pixbuf.get_has_alpha():
			transparency2 = gtk.Label(_("Yes"))
		else:
			transparency2 = gtk.Label(_("No"))
		if animtest.is_static_image():
			animation2 = gtk.Label(_("No"))
		else:
			animation2 = gtk.Label(_("Yes"))
		bits2 = gtk.Label(str(pixbuf.get_bits_per_sample()))
		channels2 = gtk.Label(str(pixbuf.get_n_channels()))
		filename2.set_alignment(0, 1)
		filedate2.set_alignment(0, 1)
		imagesize2.set_alignment(0, 1)
		filesize2.set_alignment(0, 1)
		filetype2.set_alignment(0, 1)
		transparency2.set_alignment(0, 1)
		animation2.set_alignment(0, 1)
		bits2.set_alignment(0, 1)
		channels2.set_alignment(0, 1)
		vbox_right.pack_start(filename2, False, False, 2)
		vbox_right.pack_start(filedate2, False, False, 2)
		vbox_right.pack_start(imagesize2, False, False, 2)
		vbox_right.pack_start(filesize2, False, False, 2)
		vbox_right.pack_start(filetype2, False, False, 2)
		vbox_right.pack_start(transparency2, False, False, 2)
		vbox_right.pack_start(animation2, False, False, 2)
		vbox_right.pack_start(bits2, False, False, 2)
		vbox_right.pack_start(channels2, False, False, 2)
		hbox = gtk.HBox()
		hbox.pack_start(vbox_left, False, False, 3)
		hbox.pack_start(vbox_right, False, False, 3)
		table.attach(image, 1, 2, 1, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table.attach(hbox, 2, 3, 1, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		show_props.vbox.pack_start(table, False, False, 15)
		show_props.vbox.show_all()
		close_button = show_props.add_button(gtk.STOCK_CLOSE, gtk.RESPONSE_CLOSE)
		close_button.grab_focus()
		show_props.run()
		show_props.destroy()

	def show_prefs(self, action):
		prev_thumbnail_size = self.thumbnail_size
		self.prefs_dialog = gtk.Dialog(_("Mirage Preferences"), self.window)
		self.prefs_dialog.set_has_separator(False)
		self.prefs_dialog.set_resizable(False)
		# "Interface" prefs:
		table_settings = gtk.Table(14, 3, False)
		bglabel = gtk.Label()
		bglabel.set_markup('<b>' + _('Interface') + '</b>')
		bglabel.set_alignment(0, 1)
		color_hbox = gtk.HBox(False, 0)
		colortext = gtk.Label(_('Background color:'))
		self.colorbutton = gtk.ColorButton(self.bgcolor)
		self.colorbutton.connect('color-set', self.bgcolor_selected)
		self.colorbutton.set_size_request(150, -1)
		self.colorbutton.set_tooltip_text(_("Sets the background color for the application."))
		color_hbox.pack_start(colortext, False, False, 0)
		color_hbox.pack_start(self.colorbutton, False, False, 0)
		color_hbox.pack_start(gtk.Label(), True, True, 0)
		
		simplecolor_hbox = gtk.HBox(False, 0)
		simplecolortext = gtk.Label(_('Simple background color:'))
		simplecolorbutton = gtk.CheckButton()
		simplecolorbutton.connect('toggled', self.simple_bgcolor_selected)
		simplecolor_hbox.pack_start(simplecolortext, False, False, 0)
		simplecolor_hbox.pack_start(simplecolorbutton, False, False, 0)
		simplecolor_hbox.pack_start(gtk.Label(), True, True, 0)
		if self.simple_bgcolor:
				simplecolorbutton.set_active(True)
		
		fullscreen = gtk.CheckButton(_("Open Mirage in fullscreen mode"))
		fullscreen.set_active(self.start_in_fullscreen)
		thumbbox = gtk.HBox()
		thumblabel = gtk.Label(_("Thumbnail size:"))
		thumbbox.pack_start(thumblabel, False, False, 0)
		thumbsize = gtk.combo_box_new_text()
		option = 0
		for size in self.thumbnail_sizes:
			thumbsize.append_text(size + " x " + size)
			if self.thumbnail_size == int(size):
				thumbsize.set_active(option)
			option += 1
		thumbbox.pack_start(thumbsize, False, False, 5)
		table_settings.attach(gtk.Label(), 1, 3, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_settings.attach(bglabel, 1, 3, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_settings.attach(gtk.Label(), 1, 3, 3, 4, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_settings.attach(simplecolor_hbox, 1, 2, 4, 5, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(color_hbox, 1, 2, 5, 6, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 6, 7, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_settings.attach(thumbbox, 1, 3, 7, 8, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 8, 9,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(fullscreen, 1, 3, 9, 10,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 10, 11, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 11, 12,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 12, 13,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 13, 14,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_settings.attach(gtk.Label(), 1, 3, 14, 15,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		# "Behavior" tab:
		table_behavior = gtk.Table(14, 2, False)
		openlabel = gtk.Label()
		openlabel.set_markup('<b>' + _('Open Behavior') + '</b>')
		openlabel.set_alignment(0, 1)
		hbox_openmode = gtk.HBox()
		hbox_openmode.pack_start(gtk.Label(_('Open new image in:')), False, False, 0)
		combobox = gtk.combo_box_new_text()
		combobox.append_text(_("Smart Mode"))
		combobox.append_text(_("Zoom To Fit Mode"))
		combobox.append_text(_("1:1 Mode"))
		combobox.append_text(_("Last Active Mode"))
		combobox.set_active(self.open_mode)
		hbox_openmode.pack_start(combobox, False, False, 5)
		openallimages = gtk.CheckButton(_("Load all images in current directory"))
		openallimages.set_active(self.open_all_images)
		openallimages.set_tooltip_text(_("If enabled, opening an image in Mirage will automatically load all images found in that image's directory."))
		hiddenimages = gtk.CheckButton(_("Allow loading hidden files"))
		hiddenimages.set_active(self.open_hidden_files)
		hiddenimages.set_tooltip_text(_("If checked, Mirage will open hidden files. Otherwise, hidden files will be ignored."))
		openpref = gtk.RadioButton()
		openpref1 = gtk.RadioButton(group=openpref, label=_("Use last chosen directory"))
		openpref1.set_tooltip_text(_("The default 'Open' directory will be the last directory used."))
		openpref2 = gtk.RadioButton(group=openpref, label=_("Use this fixed directory:"))
		openpref2.connect('toggled', self.prefs_use_fixed_dir_clicked)
		openpref2.set_tooltip_text(_("The default 'Open' directory will be this specified directory."))
		hbox_defaultdir = gtk.HBox()
		self.defaultdir = gtk.Button()
		hbox_defaultdir.pack_start(gtk.Label(), True, True, 0)
		hbox_defaultdir.pack_start(self.defaultdir, False, False, 0)
		hbox_defaultdir.pack_start(gtk.Label(), True, True, 0)
		if len(self.fixed_dir) > 25:
			self.defaultdir.set_label('...' + self.fixed_dir[-22:])
		else:
			self.defaultdir.set_label(self.fixed_dir)
		self.defaultdir.connect('clicked', self.defaultdir_clicked)
		self.defaultdir.set_size_request(250, -1)
		if self.use_last_dir:
			openpref1.set_active(True)
			self.defaultdir.set_sensitive(False)
		else:
			openpref2.set_active(True)
			self.defaultdir.set_sensitive(True)
		table_behavior.attach(gtk.Label(), 1, 2, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_behavior.attach(openlabel, 1, 2, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_behavior.attach(gtk.Label(), 1, 2, 3, 4, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_behavior.attach(hbox_openmode, 1, 2, 4, 5, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_behavior.attach(gtk.Label(), 1, 2, 5, 6, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_behavior.attach(openallimages, 1, 2, 6, 7, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_behavior.attach(hiddenimages, 1, 2, 7, 8, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_behavior.attach(gtk.Label(), 1, 2, 8, 9, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_behavior.attach(openpref1, 1, 2, 9, 10, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_behavior.attach(openpref2, 1, 2, 10, 11, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_behavior.attach(hbox_defaultdir, 1, 2, 11, 12, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 45, 0)
		table_behavior.attach(gtk.Label(), 1, 2, 12, 13, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 45, 0)
		# "Navigation" tab:
		table_navigation = gtk.Table(14, 2, False)
		navlabel = gtk.Label()
		navlabel.set_markup('<b>' + _('Navigation') + '</b>')
		navlabel.set_alignment(0, 1)
		preloadnav = gtk.CheckButton(label=_("Preload images for faster navigation"))
		preloadnav.set_active(self.preloading_images)
		preloadnav.set_tooltip_text(_("If enabled, the next and previous images in the list will be preloaded during idle time. Note that the speed increase comes at the expense of memory usage, so it is recommended to disable this option on machines with limited ram."))
		hbox_listwrap = gtk.HBox()
		hbox_listwrap.pack_start(gtk.Label(_("Wrap around imagelist:")), False, False, 0)
		combobox2 = gtk.combo_box_new_text()
		combobox2.append_text(_("No"))
		combobox2.append_text(_("Yes"))
		combobox2.append_text(_("Prompt User"))
		combobox2.set_active(self.listwrap_mode)
		hbox_listwrap.pack_start(combobox2, False, False, 5)
		table_navigation.attach(gtk.Label(), 1, 2, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_navigation.attach(navlabel, 1, 2, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 3, 4, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_navigation.attach(hbox_listwrap, 1, 2, 4, 5, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 5, 6, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_navigation.attach(preloadnav, 1, 2, 6, 7, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 7, 8, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 8, 9, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 9, 10, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 10, 11, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 11, 12, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 12, 13, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_navigation.attach(gtk.Label(), 1, 2, 13, 14, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		# "Slideshow" tab:
		table_slideshow = gtk.Table(14, 2, False)
		slideshowlabel = gtk.Label()
		slideshowlabel.set_markup('<b>' + _('Slideshow Mode') + '</b>')
		slideshowlabel.set_alignment(0, 1)
		hbox_delay = gtk.HBox()
		hbox_delay.pack_start(gtk.Label(_("Delay between images in seconds:")), False, False, 0)
		spin_adj = gtk.Adjustment(self.slideshow_delay, 0, 50000, 1, 10, 0)
		delayspin = gtk.SpinButton(spin_adj, 1.0, 0)
		delayspin.set_numeric(True)
		hbox_delay.pack_start(delayspin, False, False, 5)
		randomize = gtk.CheckButton(_("Randomize order of images"))
		randomize.set_active(self.slideshow_random)
		randomize.set_tooltip_text(_("If enabled, a random image will be chosen during slideshow mode (without loading any image twice)."))
		disable_screensaver = gtk.CheckButton(_("Disable screensaver in slideshow mode"))
		disable_screensaver.set_active(self.disable_screensaver)
		disable_screensaver.set_tooltip_text(_("If enabled, xscreensaver will be temporarily disabled during slideshow mode."))
		ss_in_fs = gtk.CheckButton(_("Always start in fullscreen mode"))
		ss_in_fs.set_tooltip_text(_("If enabled, starting a slideshow will put the application in fullscreen mode."))
		ss_in_fs.set_active(self.slideshow_in_fullscreen)
		table_slideshow.attach(gtk.Label(), 1, 2, 1, 2, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(slideshowlabel, 1, 2, 2, 3, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 3, 4, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(hbox_delay, 1, 2, 4, 5, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 5, 6, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(disable_screensaver, 1, 2, 6, 7, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_slideshow.attach(ss_in_fs, 1, 2, 7, 8, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_slideshow.attach(randomize, 1, 2, 8, 9, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 9, 10, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 10, 11, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 11, 12, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 12, 13, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		table_slideshow.attach(gtk.Label(), 1, 2, 13, 14, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 0, 0)
		# "Image" tab:
		table_image = gtk.Table(14, 2, False)
		imagelabel = gtk.Label()
		imagelabel.set_markup('<b>' + _('Image Editing') + '</b>')
		imagelabel.set_alignment(0, 1)
		deletebutton = gtk.CheckButton(_("Confirm image delete"))
		deletebutton.set_active(self.confirm_delete)
		
		zoom_hbox = gtk.HBox()
		zoom_hbox.pack_start(gtk.Label(_('Scaling quality:')), False, False, 0)
		zoomcombo = gtk.combo_box_new_text()
		zoomcombo.append_text(_("Nearest (Fastest)"))
		zoomcombo.append_text(_("Tiles"))
		zoomcombo.append_text(_("Bilinear"))
		zoomcombo.append_text(_("Hyper (Best)"))
		zoomcombo.set_active(self.zoomvalue)
		zoom_hbox.pack_start(zoomcombo, False, False, 0)
		zoom_hbox.pack_start(gtk.Label(), True, True, 0)
		
		hbox_save = gtk.HBox()
		savelabel = gtk.Label(_("Modified images:"))
		savecombo = gtk.combo_box_new_text()
		savecombo.append_text(_("Ignore Changes"))
		savecombo.append_text(_("Auto-Save"))
		savecombo.append_text(_("Prompt For Action"))
		savecombo.set_active(self.savemode)
		hbox_save.pack_start(savelabel, False, False, 0)
		hbox_save.pack_start(savecombo, False, False, 5)
		
		hbox_quality = gtk.HBox()
		qualitylabel = gtk.Label(_("Quality to save in:"))
		qspin_adj = gtk.Adjustment(self.quality_save, 0, 100, 1, 100, 0)
		qualityspin = gtk.SpinButton(qspin_adj, 1.0, 0)
		qualityspin.set_numeric(True)
		hbox_quality.pack_start(qualitylabel, False, False, 0)
		hbox_quality.pack_start(qualityspin, False, False, 5)
		table_image.attach(gtk.Label(), 1, 3, 1, 2,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(imagelabel, 1, 3, 2, 3,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 15, 0)
		table_image.attach(gtk.Label(), 1, 3, 3, 4,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(zoom_hbox, 1, 3, 4, 5,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 5, 6,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(hbox_save, 1, 3, 6, 7, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 7, 8, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(hbox_quality, 1, 3, 8, 9, gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 9, 10,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(deletebutton, 1, 3, 10, 11,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 11, 12,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 12, 13,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 13, 14,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		table_image.attach(gtk.Label(), 1, 3, 14, 15,  gtk.FILL|gtk.EXPAND, gtk.FILL|gtk.EXPAND, 30, 0)
		# Add tabs:
		notebook = gtk.Notebook()
		notebook.append_page(table_behavior, gtk.Label(_("Behavior")))
		notebook.append_page(table_navigation, gtk.Label(_("Navigation")))
		notebook.append_page(table_settings, gtk.Label(_("Interface")))
		notebook.append_page(table_slideshow, gtk.Label(_("Slideshow")))
		notebook.append_page(table_image, gtk.Label(_("Image")))
		notebook.set_current_page(0)
		hbox = gtk.HBox()
		self.prefs_dialog.vbox.pack_start(hbox, False, False, 7)
		hbox.pack_start(notebook, False, False, 7)
		notebook.connect('switch-page', self.prefs_tab_switched)
		# Show prefs:
		self.prefs_dialog.vbox.show_all()
		self.close_button = self.prefs_dialog.add_button(gtk.STOCK_CLOSE, gtk.RESPONSE_CLOSE)
		self.close_button.grab_focus()
		response = self.prefs_dialog.run()
		if response == gtk.RESPONSE_CLOSE or response == gtk.RESPONSE_DELETE_EVENT:
			self.zoomvalue = zoomcombo.get_active()
			if int(round(self.zoomvalue, 0)) == 0:
				self.zoom_quality = gtk.gdk.INTERP_NEAREST
			elif int(round(self.zoomvalue, 0)) == 1:
				self.zoom_quality = gtk.gdk.INTERP_TILES
			elif int(round(self.zoomvalue, 0)) == 2:
				self.zoom_quality = gtk.gdk.INTERP_BILINEAR
			elif int(round(self.zoomvalue, 0)) == 3:
				self.zoom_quality = gtk.gdk.INTERP_HYPER
			self.open_all_images = openallimages.get_active()
			self.open_hidden_files = hiddenimages.get_active()
			if openpref1.get_active():
				self.use_last_dir = True
			else:
				self.use_last_dir = False
			open_mode_prev = self.open_mode
			self.open_mode = combobox.get_active()
			preloading_images_prev = self.preloading_images
			self.preloading_images = preloadnav.get_active()
			self.listwrap_mode = combobox2.get_active()
			self.slideshow_delay = delayspin.get_value()
			self.curr_slideshow_delay = self.slideshow_delay
			self.slideshow_random = randomize.get_active()
			self.curr_slideshow_random = self.slideshow_random
			self.disable_screensaver = disable_screensaver.get_active()
			self.slideshow_in_fullscreen = ss_in_fs.get_active()
			self.savemode = savecombo.get_active()
			self.start_in_fullscreen = fullscreen.get_active()
			self.confirm_delete = deletebutton.get_active()
			self.quality_save = qualityspin.get_value()
			self.thumbnail_size = int(self.thumbnail_sizes[thumbsize.get_active()])
			if self.thumbnail_size != prev_thumbnail_size:
				gobject.idle_add(self.thumbpane_set_size)
				gobject.idle_add(self.thumbpane_update_images, True, self.curr_img_in_list)
			self.prefs_dialog.destroy()
			self.set_go_navigation_sensitivities(False)
			if (self.preloading_images and not preloading_images_prev) or (open_mode_prev != self.open_mode):
				# The user just turned on preloading, so do it:
				self.preloadimg_next_in_list = -1
				self.preloadimg_prev_in_list = -1
				self.preload_when_idle = gobject.idle_add(self.preload_next_image, False)
				self.preload_when_idle2 = gobject.idle_add(self.preload_prev_image, False)
			elif not self.preloading_images:
				self.preloadimg_next_in_list = -1
				self.preloadimg_prev_in_list = -1

	def prefs_use_fixed_dir_clicked(self, button):
		if button.get_active():
			self.defaultdir.set_sensitive(True)
		else:
			self.defaultdir.set_sensitive(False)

	def rename_image(self, action):
		if len(self.image_list) > 0:
			temp_slideshow_mode = self.slideshow_mode
			if self.slideshow_mode:
				self.toggle_slideshow(None)
			rename_dialog = gtk.Dialog(_('Rename Image'), self.window, gtk.DIALOG_MODAL)
			self.rename_txt = gtk.Entry()
			filename = os.path.basename(self.currimg_name)
			self.rename_txt.set_text(filename)
			self.rename_txt.set_activates_default(True)
			cancelbutton = rename_dialog.add_button(gtk.STOCK_CANCEL, gtk.RESPONSE_CANCEL)
			renamebutton = rename_dialog.add_button(_("_Rename"), gtk.RESPONSE_ACCEPT)
			renameimage = gtk.Image()
			renameimage.set_from_stock(gtk.STOCK_OK, gtk.ICON_SIZE_BUTTON)
			renamebutton.set_image(renameimage)
			animtest = gtk.gdk.PixbufAnimation(self.currimg_name)
			if animtest.is_static_image():
				pixbuf, image_width, image_height = self.get_pixbuf_of_size(self.currimg_pixbuf_original, 60, self.zoom_quality)
			else:
				pixbuf, image_width, image_height = self.get_pixbuf_of_size(animtest.get_static_image(), 60, self.zoom_quality)
			image = gtk.Image()
			image.set_from_pixbuf(pixbuf)
			instructions = gtk.Label(_("Enter the new name:"))
			instructions.set_alignment(0, 1)
			hbox = gtk.HBox()
			hbox.pack_start(image, False, False, 10)
			vbox_stuff = gtk.VBox()
			vbox_stuff.pack_start(gtk.Label(), False, False, 0)
			vbox_stuff.pack_start(instructions, False, False, 0)
			vbox_stuff.pack_start(gtk.Label(), False, False, 0)
			vbox_stuff.pack_start(self.rename_txt, True, True, 0)
			vbox_stuff.pack_start(gtk.Label(), False, False, 0)
			hbox.pack_start(vbox_stuff, True, True, 10)
			rename_dialog.vbox.pack_start(hbox, False, False, 0)
			rename_dialog.set_has_separator(True)
			rename_dialog.set_default_response(gtk.RESPONSE_ACCEPT)
			rename_dialog.set_size_request(300, -1)
			rename_dialog.vbox.show_all()
			rename_dialog.connect('show', self.select_rename_text)
			response = rename_dialog.run()
			if response == gtk.RESPONSE_ACCEPT:
				try:
					new_filename = os.path.dirname(self.currimg_name) + "/" + self.rename_txt.get_text()
					shutil.move(self.currimg_name, new_filename)
					# Update thumbnail filename:
					try:
						shutil.move(self_get_name(self.currimg_name)[1], self.thumbnail_get_name(new_filename)[1])
					except:
						pass
					self.recent_file_remove_and_refresh_name(self.currimg_name)
					self.currimg_name = new_filename
					self.register_file_with_recent_docs(self.currimg_name)
					self.update_title()
				except:
					error_dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_OK, _('Unable to rename %s') % self.currimg_name)
					error_dialog.set_title(_("Unable to rename"))
					error_dialog.run()
					error_dialog.destroy()
			rename_dialog.destroy()
			if temp_slideshow_mode:
				self.toggle_slideshow(None)

	def select_rename_text(self, widget):
		filename = os.path.basename(self.currimg_name)
		fileext = os.path.splitext(os.path.basename(self.currimg_name))[1]
		self.rename_txt.select_region(0, len(filename) - len(fileext))

	def delete_image(self, action):
		if len(self.image_list) > 0:
			temp_slideshow_mode = self.slideshow_mode
			if self.slideshow_mode:
				self.toggle_slideshow(None)
			delete_dialog = gtk.Dialog(_('Delete Image'), self.window, gtk.DIALOG_MODAL)
			if self.confirm_delete:
				permlabel = gtk.Label(_('Are you sure you wish to permanently delete %s?') % os.path.split(self.currimg_name)[1])
				permlabel.set_line_wrap(True)
				permlabel.set_alignment(0, 0.1)
				warningicon = gtk.Image()
				warningicon.set_from_stock(gtk.STOCK_DIALOG_WARNING, gtk.ICON_SIZE_DIALOG)
				hbox = gtk.HBox()
				hbox.pack_start(warningicon, False, False, 10)
				hbox.pack_start(permlabel, False, False, 10)
				delete_dialog.vbox.pack_start(gtk.Label(), False, False, 0)
				delete_dialog.vbox.pack_start(hbox, False, False, 0)
				cancelbutton = delete_dialog.add_button(gtk.STOCK_CANCEL, gtk.RESPONSE_CANCEL)
				deletebutton = delete_dialog.add_button(gtk.STOCK_DELETE, gtk.RESPONSE_YES)
				delete_dialog.set_has_separator(False)
				deletebutton.set_property('has-focus', True)
				delete_dialog.set_default_response(gtk.RESPONSE_YES)
				delete_dialog.vbox.show_all()
				response = delete_dialog.run()
			else:
				response = gtk.RESPONSE_YES
			if response  == gtk.RESPONSE_YES:
				try:
					os.remove(self.currimg_name)
					self.image_modified = False
					try:
						os.remove(self.thumbnail_get_name(self.currimg_name)[1])
					except:
						pass
					self.recent_file_remove_and_refresh_name(self.currimg_name)
					iter = self.thumblist.get_iter((self.curr_img_in_list,))
					try:
						self.thumbnail_loaded.pop(self.curr_img_in_list)
						self.thumbpane_update_images()
					except:
						pass
					self.thumblist.remove(iter)
					templist = self.image_list
					self.image_list = []
					for item in templist:
						if item != self.currimg_name:
							self.image_list.append(item)
					if len(self.image_list) >= 1:
						if len(self.image_list) == 1:
							self.curr_img_in_list = 0
						elif self.curr_img_in_list == len(self.image_list):
							self.curr_img_in_list -= 1
						self.change_cursor(gtk.gdk.Cursor(gtk.gdk.WATCH))
						self.preloadimg_prev_in_list = -1
						self.preloadimg_next_in_list = -1
						self.load_when_idle = gobject.idle_add(self.load_new_image, False, False, True, True, True, True)
						self.set_go_navigation_sensitivities(False)
					else:
						self.imageview.clear()
						self.update_title()
						self.statusbar.push(self.statusbar.get_context_id(""), "")
						self.image_loaded = False
						self.set_slideshow_sensitivities()
						self.set_image_sensitivities(False)
						self.set_go_navigation_sensitivities(False)
					# Select new item:
					self.thumbpane_select(self.curr_img_in_list)
				except:
					error_dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_OK, _('Unable to delete %s') % self.currimg_name)
					error_dialog.set_title(_("Unable to delete"))
					error_dialog.run()
					error_dialog.destroy()
			delete_dialog.destroy()
			if temp_slideshow_mode:
				self.toggle_slideshow(None)

	def defaultdir_clicked(self, button):
		getdir = gtk.FileChooserDialog(title=_("Choose directory"),action=gtk.FILE_CHOOSER_ACTION_OPEN,buttons=(gtk.STOCK_CANCEL,gtk.RESPONSE_CANCEL,gtk.STOCK_OPEN,gtk.RESPONSE_OK))
		getdir.set_action(gtk.FILE_CHOOSER_ACTION_SELECT_FOLDER)
		getdir.set_filename(self.fixed_dir)
		getdir.set_default_response(gtk.RESPONSE_OK)
		response = getdir.run()
		if response == gtk.RESPONSE_OK:
			self.fixed_dir = getdir.get_filenames()[0]
			if len(self.fixed_dir) > 25:
				button.set_label('...' + self.fixed_dir[-22:])
			else:
				button.set_label(self.fixed_dir)
			getdir.destroy()
		else:
			getdir.destroy()

	def prefs_tab_switched(self, notebook, page, page_num):
		do_when_idle = gobject.idle_add(self.grab_close_button)

	def grab_close_button(self):
		self.close_button.grab_focus()

	def bgcolor_selected(self, widget):
		# When the user selects a color, store this color in self.bgcolor (which will
		# later be saved to .miragerc) and set this background color:
		self.bgcolor = widget.get_property('color')
		if not self.simple_bgcolor:
			self.layout.modify_bg(gtk.STATE_NORMAL, self.bgcolor)
			self.slideshow_window.modify_bg(gtk.STATE_NORMAL, self.bgcolor)
			self.slideshow_window2.modify_bg(gtk.STATE_NORMAL, self.bgcolor)

	def simple_bgcolor_selected(self, widget):
		if widget.get_active():
			self.simple_bgcolor = True
			self.layout.modify_bg(gtk.STATE_NORMAL, None)
		else:
			self.simple_bgcolor = False
			self.bgcolor_selected(self.colorbutton)

	def show_about(self, action):
		# Help > About
		self.about_dialog = gtk.AboutDialog()
		try:
			self.about_dialog.set_transient_for(self.window)
			self.about_dialog.set_modal(True)
		except:
			pass
		self.about_dialog.set_name('Mirage')
		self.about_dialog.set_version(__version__)
		self.about_dialog.set_comments(_('A fast GTK+ Image Viewer.'))
		self.about_dialog.set_license(__license__)
		self.about_dialog.set_authors(['Scott Horowitz <stonecrest@gmail.com>', 'Fredric Johansson <fredric.miscmail@gmail.com>'])
		self.about_dialog.set_artists(['William Rea <sillywilly@gmail.com>'])
		self.about_dialog.set_translator_credits('cs - Petr Pisar <petr.pisar@atlas.cz>\nde - Bjoern Martensen <bjoern.martensen@gmail.com>\nes - Isidro Arribas <cdhotfire@gmail.com>\nfr - Mike Massonnet <mmassonnet@gmail.com>\nhu - Sandor Lisovszki <lisovszki@dunakanyar.net>\nnl - Pascal De Vuyst <pascal.devuyst@gmail.com>\npl - Tomasz Dominikowski <dominikowski@gmail.com>\npt_BR - Danilo Martins <mawkee@gmail.com>\nru - mavka <mavka@justos.org>\nit - Daniele Maggio <dado84@freemail.it>\nzh_CN - Jayden Suen <no.sun@163.com>')
		gtk.about_dialog_set_url_hook(self.show_website, "http://mirageiv.berlios.de")
		self.about_dialog.set_website_label("http://mirageiv.berlios.de")
		icon_path = self.find_path('mirage.png')
		try:
			icon_pixbuf = gtk.gdk.pixbuf_new_from_file(icon_path)
			self.about_dialog.set_logo(icon_pixbuf)
		except:
			pass
		self.about_dialog.connect('response', self.close_about)
		self.about_dialog.connect('delete_event', self.close_about)
		self.about_dialog.show_all()

	def show_website(self, dialog, blah, link):
		self.browser_load(link)

	def show_help(self, action):
		self.browser_load("http://mirageiv.berlios.de/docs.html")

	def browser_load(self, docslink):
		try:
			pid = subprocess.Popen(["chromium-browser", docslink]).pid
		except:
			try:
				pid = subprocess.Popen(["x-www-browser", docslink]).pid
			except:
				try:
					pid = subprocess.Popen(["gnome-open", docslink]).pid
				except:
					try:
						pid = subprocess.Popen(["exo-open", docslink]).pid
					except:
						try:
							pid = subprocess.Popen(["kfmclient", "openURL", docslink]).pid
						except:
							try:
								pid = subprocess.Popen(["firefox", docslink]).pid
							except:
								try:
									pid = subprocess.Popen(["mozilla", docslink]).pid
								except:
									try:
										pid = subprocess.Popen(["opera", docslink]).pid
									except:
										error_dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL, gtk.MESSAGE_WARNING, gtk.BUTTONS_CLOSE, _('Unable to launch a suitable browser.'))
										error_dialog.run()
										error_dialog.destroy()

	def close_about(self, event, data=None):
		self.about_dialog.hide()
		return True

	def mousewheel_scrolled(self, widget, event):
		if event.type == gtk.gdk.SCROLL:
			# Zooming of the image by Ctrl-mousewheel
			if event.state & gtk.gdk.CONTROL_MASK:
				if event.direction == gtk.gdk.SCROLL_UP:
					self.zoom_in(None)
				elif event.direction == gtk.gdk.SCROLL_DOWN:
					self.zoom_out(None)
				return True
			# Navigation of images with mousewheel:
			else:
				if event.direction == gtk.gdk.SCROLL_UP:
					self.goto_prev_image(None)
				elif event.direction == gtk.gdk.SCROLL_DOWN:
					self.goto_next_image(None)
				return True

	def mouse_moved(self, widget, event):
		# This handles the panning of the image
		if event.is_hint:
			x, y, state = event.window.get_pointer()
		else:
			state = event.state
		x, y = event.x_root, event.y_root
		if (state & gtk.gdk.BUTTON2_MASK) or (state & gtk.gdk.BUTTON1_MASK):
			# Prevent self.expose_event() from potentially further changing the
			# adjustments upon the adjustment value changes
			self.updating_adjustments = True
			xadjust = self.layout.get_hadjustment()
			newx = xadjust.value + (self.prevmousex - x)
			if newx >= xadjust.lower and newx <= xadjust.upper - xadjust.page_size:
				xadjust.set_value(newx)
				self.layout.set_hadjustment(xadjust)
			yadjust = self.layout.get_vadjustment()
			newy = yadjust.value + (self.prevmousey - y)
			if newy >= yadjust.lower and newy <= yadjust.upper - yadjust.page_size:
				yadjust.set_value(newy)
				self.layout.set_vadjustment(yadjust)
			self.updating_adjustments = False
		self.prevmousex = x
		self.prevmousey = y
		if self.fullscreen_mode:
			# Show cursor on movement, then hide after 2 seconds of no movement
			self.change_cursor(None)
			if not self.slideshow_controls_visible:
				gobject.source_remove(self.timer_id)
				if not self.closing_app:
					while gtk.events_pending():
						gtk.main_iteration()
				self.timer_id = gobject.timeout_add(2000, self.hide_cursor)
			if y > 0.9*self.available_image_height():
				self.slideshow_controls_show()
			else:
				self.slideshow_controls_hide()
		return True

	def button_pressed(self, widget, event):
		if self.image_loaded:
			# Changes the cursor to the 'resize' cursor, like GIMP, on a middle click:
			if (event.button == 2 or event.button == 1) and (self.hscroll.get_property('visible')==True or self.vscroll.get_property('visible')==True):
				self.change_cursor(gtk.gdk.Cursor(gtk.gdk.FLEUR))
				self.prevmousex = event.x_root
				self.prevmousey = event.y_root
			# Right-click popup:
			elif self.image_loaded and event.button == 3:
				self.UIManager.get_widget('/Popup').popup(None, None, None, event.button, event.time)
		return True

	def button_released(self, widget, event):
		# Resets the cursor when middle mouse button is released
		if event.button == 2 or event.button == 1:
			self.change_cursor(None)
		return True

	def zoom_in(self, action):
		if self.currimg_name != "" and self.UIManager.get_widget('/MainMenu/ViewMenu/In').get_property('sensitive'):
			self.image_zoomed = True
			self.currimg_zoomratio = self.currimg_zoomratio * 1.25
			self.set_zoom_sensitivities()
			self.last_image_action_was_fit = False
			self.put_zoom_image_to_window(False)
			self.update_statusbar()

	def zoom_out(self, action):
		if self.currimg_name != "" and self.UIManager.get_widget('/MainMenu/ViewMenu/Out').get_property('sensitive'):
			if self.currimg_zoomratio == self.min_zoomratio:
				# No point in proceeding..
				return
			self.image_zoomed = True
			self.currimg_zoomratio = self.currimg_zoomratio * 1/1.25
			if self.currimg_zoomratio < self.min_zoomratio:
				self.currimg_zoomratio = self.min_zoomratio
			self.set_zoom_sensitivities()
			self.last_image_action_was_fit = False
			self.put_zoom_image_to_window(False)
			self.update_statusbar()

	def zoom_to_fit_window_action(self, action):
		self.zoom_to_fit_window(action, False, False)

	def zoom_to_fit_window(self, action, is_preloadimg_next, is_preloadimg_prev):
		if is_preloadimg_next:
			if self.preloading_images and self.preloadimg_next_in_list != -1:
				win_width = self.available_image_width()
				win_height = self.available_image_height()
				preimg_width = self.preloadimg_next_pixbuf_original.get_width()
				preimg_height = self.preloadimg_next_pixbuf_original.get_height()
				prewidth_ratio = float(preimg_width)/win_width
				preheight_ratio = float(preimg_height)/win_height
				if prewidth_ratio < preheight_ratio:
					premax_ratio = preheight_ratio
				else:
					premax_ratio = prewidth_ratio
				self.preloadimg_next_zoomratio = 1/float(max_ratio)
		elif is_preloadimg_prev:
			if self.preloading_images and self.preloadimg_prev_in_list != -1:
				win_width = self.available_image_width()
				win_height = self.available_image_height()
				preimg_width = self.preloadimg_prev_pixbuf_original.get_width()
				preimg_height = self.preloadimg_prev_pixbuf_original.get_height()
				prewidth_ratio = float(preimg_width)/win_width
				preheight_ratio = float(preimg_height)/win_height
				if prewidth_ratio < preheight_ratio:
					premax_ratio = preheight_ratio
				else:
					premax_ratio = prewidth_ratio
				self.preloadimg_prev_zoomratio = 1/float(max_ratio)
		else:
			if self.currimg_name != "" and (self.slideshow_mode or self.UIManager.get_widget('/MainMenu/ViewMenu/Fit').get_property('sensitive')):
				self.image_zoomed = True
				self.last_mode = self.open_mode_fit
				self.last_image_action_was_fit = True
				self.last_image_action_was_smart_fit = False
				# Calculate zoomratio needed to fit to window:
				win_width = self.available_image_width()
				win_height = self.available_image_height()
				img_width = self.currimg_pixbuf_original.get_width()
				img_height = self.currimg_pixbuf_original.get_height()
				width_ratio = float(img_width)/win_width
				height_ratio = float(img_height)/win_height
				if width_ratio < height_ratio:
					max_ratio = height_ratio
				else:
					max_ratio = width_ratio
				self.currimg_zoomratio = 1/float(max_ratio)
				self.set_zoom_sensitivities()
				self.put_zoom_image_to_window(False)
				self.update_statusbar()

	def zoom_to_fit_or_1_to_1(self, action, is_preloadimg_next, is_preloadimg_prev):
		if is_preloadimg_next:
			if self.preloading_images and self.preloadimg_next_in_list != -1:
				win_width = self.available_image_width()
				win_height = self.available_image_height()
				preimg_width = self.preloadimg_next_pixbuf_original.get_width()
				preimg_height = self.preloadimg_next_pixbuf_original.get_height()
				prewidth_ratio = float(preimg_width)/win_width
				preheight_ratio = float(preimg_height)/win_height
				if prewidth_ratio < preheight_ratio:
					premax_ratio = preheight_ratio
				else:
					premax_ratio = prewidth_ratio
				self.preloadimg_next_zoomratio = 1/float(premax_ratio)
				if self.preloadimg_next_zoomratio > 1:
					self.preloadimg_next_zoomratio = 1
		elif is_preloadimg_prev:
			if self.preloading_images and self.preloadimg_prev_in_list != -1:
				win_width = self.available_image_width()
				win_height = self.available_image_height()
				preimg_width = self.preloadimg_prev_pixbuf_original.get_width()
				preimg_height = self.preloadimg_prev_pixbuf_original.get_height()
				prewidth_ratio = float(preimg_width)/win_width
				preheight_ratio = float(preimg_height)/win_height
				if prewidth_ratio < preheight_ratio:
					premax_ratio = preheight_ratio
				else:
					premax_ratio = prewidth_ratio
				self.preloadimg_prev_zoomratio = 1/float(premax_ratio)
				if self.preloadimg_prev_zoomratio > 1:
					self.preloadimg_prev_zoomratio = 1
		else:
			if self.currimg_name != "":
				self.image_zoomed = True
				# Calculate zoomratio needed to fit to window:
				win_width = self.available_image_width()
				win_height = self.available_image_height()
				img_width = self.currimg_pixbuf_original.get_width()
				img_height = self.currimg_pixbuf_original.get_height()
				width_ratio = float(img_width)/win_width
				height_ratio = float(img_height)/win_height
				if width_ratio < height_ratio:
					max_ratio = height_ratio
				else:
					max_ratio = width_ratio
				self.currimg_zoomratio = 1/float(max_ratio)
				self.set_zoom_sensitivities()
				if self.currimg_zoomratio > 1:
					# Revert to 1:1 zoom
					self.zoom_1_to_1(action, False, False)
				else:
					self.put_zoom_image_to_window(False)
					self.update_statusbar()
				self.last_image_action_was_fit = True
				self.last_image_action_was_smart_fit = True

	def zoom_1_to_1_action(self, action):
		self.zoom_1_to_1(action, False, False)

	def zoom_1_to_1(self, action, is_preloadimg_next, is_preloadimg_prev):
		if is_preloadimg_next:
			if self.preloading_images:
				self.preloadimg_next_zoomratio = 1
		elif is_preloadimg_prev:
			if self.preloading_images:
				self.preloadimg_prev_zoomratio = 1
		else:
			if self.currimg_name != "" and (self.slideshow_mode or self.currimg_is_animation or (not self.currimg_is_animation and self.UIManager.get_widget('/MainMenu/ViewMenu/1:1').get_property('sensitive'))):
				self.image_zoomed = True
				self.last_mode = self.open_mode_1to1
				self.last_image_action_was_fit = False
				self.currimg_zoomratio = 1
				self.put_zoom_image_to_window(False)
				self.update_statusbar()

	def rotate_left(self, action):
		self.rotate_left_or_right(self.UIManager.get_widget('/MainMenu/EditMenu/Rotate Left'), 90)

	def rotate_right(self, action):
		self.rotate_left_or_right(self.UIManager.get_widget('/MainMenu/EditMenu/Rotate Right'), 270)
	
	def rotate_left_or_right(self, widget, angle):
		if self.currimg_name != "" and widget.get_property('sensitive'):
			self.currimg_pixbuf_original = self.image_rotate(self.currimg_pixbuf_original, angle)
			if self.last_image_action_was_fit:
				if self.last_image_action_was_smart_fit:
					self.zoom_to_fit_or_1_to_1(None, False, False)
				else:
					self.zoom_to_fit_window(None, False, False)
			else:
				self.currimg_width, self.currimg_height = self.currimg_height, self.currimg_width
				self.layout.set_size(self.currimg_width, self.currimg_height)
				self.currimg_pixbuf = self.image_rotate(self.currimg_pixbuf, angle)
				self.imageview.set_from_pixbuf(self.currimg_pixbuf)
				self.show_scrollbars_if_needed()
				self.center_image()
				self.update_statusbar()
			self.image_modified = True
		

	def flip_image_vert(self, action):
		self.flip_image_vert_or_horiz(self.UIManager.get_widget('/MainMenu/EditMenu/Flip Vertically'), True)

	def flip_image_horiz(self, action):
		self.flip_image_vert_or_horiz(self.UIManager.get_widget('/MainMenu/EditMenu/Flip Horizontally'), False)
			
	def flip_image_vert_or_horiz(self, widget, vertical):
		if self.currimg_name != "" and widget.get_property('sensitive'):
			self.currimg_pixbuf = self.image_flip(self.currimg_pixbuf, vertical)
			self.currimg_pixbuf_original = self.image_flip(self.currimg_pixbuf_original, vertical)
			self.imageview.set_from_pixbuf(self.currimg_pixbuf)
			self.image_modified = True
		
	def get_pixbuf_of_size(self, pixbuf, size, zoom_quality):
		# Creates a pixbuf that fits in the specified square of sizexsize
		# while preserving the aspect ratio
		# Returns tuple: (scaled_pixbuf, actual_width, actual_height)
		image_width = pixbuf.get_width()
		image_height = pixbuf.get_height()
		if image_width-size > image_height-size:
			if image_width > size:
				image_height = int(size/float(image_width)*image_height)
				image_width = size
		else:
			if image_height > size:
				image_width = int(size/float(image_height)*image_width)
				image_height = size
		if not pixbuf.get_has_alpha():
			crop_pixbuf = pixbuf.scale_simple(image_width, image_height, zoom_quality)
		else:
			colormap = self.imageview.get_colormap()
			light_grey = colormap.alloc_color('#666666', True, True)
			dark_grey = colormap.alloc_color('#999999', True, True)
			crop_pixbuf = pixbuf.composite_color_simple(image_width, image_height, zoom_quality, 255, 8, light_grey.pixel, dark_grey.pixel)
		return (crop_pixbuf, image_width, image_height)

	def pixbuf_add_border(self, pix):
		# Add a gray outline to pix. This will increase the pixbuf size by
		# 2 pixels lengthwise and heightwise, 1 on each side. Returns pixbuf.
		try:
			width = pix.get_width()
			height = pix.get_height()
			newpix = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, True, 8, width+2, height+2)
			newpix.fill(0x858585ff)
			pix.copy_area(0, 0, width, height, newpix, 1, 1)
			return newpix
		except:
			return pix

	def crop_image(self, action):
		dialog = gtk.Dialog(_("Crop Image"), self.window, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT))
		cropbutton = dialog.add_button(_("C_rop"), gtk.RESPONSE_ACCEPT)
		cropimage = gtk.Image()
		cropimage.set_from_stock(gtk.STOCK_OK, gtk.ICON_SIZE_BUTTON)
		cropbutton.set_image(cropimage)
		image = gtk.DrawingArea()
		crop_pixbuf, image_width, image_height = self.get_pixbuf_of_size(self.currimg_pixbuf_original, 400, self.zoom_quality)
		image.set_size_request(image_width, image_height)
		hbox = gtk.HBox()
		hbox.pack_start(gtk.Label(), expand=True)
		hbox.pack_start(image, expand=False)
		hbox.pack_start(gtk.Label(), expand=True)
		vbox_left = gtk.VBox()
		x_adj = gtk.Adjustment(0, 0, self.currimg_pixbuf_original.get_width(), 1, 10, 0)
		x = gtk.SpinButton(x_adj, 0, 0)
		x.set_numeric(True)
		x.set_update_policy(gtk.UPDATE_IF_VALID)
		x.set_wrap(False)
		x_label = gtk.Label("X:")
		x_label.set_alignment(0, 0.7)
		y_adj = gtk.Adjustment(0, 0, self.currimg_pixbuf_original.get_height(), 1, 10, 0)
		y = gtk.SpinButton(y_adj, 0, 0)
		y.set_numeric(True)
		y.set_update_policy(gtk.UPDATE_IF_VALID)
		y.set_wrap(False)
		y_label = gtk.Label("Y:")
		x_label.set_size_request(y_label.size_request()[0], -1)
		hbox_x = gtk.HBox()
		hbox_y = gtk.HBox()
		hbox_x.pack_start(x_label, False, False, 10)
		hbox_x.pack_start(x, False, False, 0)
		hbox_x.pack_start(gtk.Label(), False, False, 3)
		hbox_y.pack_start(y_label, False, False, 10)
		hbox_y.pack_start(y, False, False, 0)
		hbox_y.pack_start(gtk.Label(), False, False, 3)
		vbox_left.pack_start(hbox_x, False, False, 0)
		vbox_left.pack_start(hbox_y, False, False, 0)
		vbox_right = gtk.VBox()
		width_adj = gtk.Adjustment(self.currimg_pixbuf_original.get_width(), 1, self.currimg_pixbuf_original.get_width(), 1, 10, 0)
		width = gtk.SpinButton(width_adj, 0, 0)
		width.set_numeric(True)
		width.set_update_policy(gtk.UPDATE_IF_VALID)
		width.set_wrap(False)
		width_label = gtk.Label(_("Width:"))
		width_label.set_alignment(0, 0.7)
		height_adj = gtk.Adjustment(self.currimg_pixbuf_original.get_height(), 1, self.currimg_pixbuf_original.get_height(), 1, 10, 0)
		height = gtk.SpinButton(height_adj, 0, 0)
		height.set_numeric(True)
		height.set_update_policy(gtk.UPDATE_IF_VALID)
		height.set_wrap(False)
		height_label = gtk.Label(_("Height:"))
		width_label.set_size_request(height_label.size_request()[0], -1)
		height_label.set_alignment(0, 0.7)
		hbox_width = gtk.HBox()
		hbox_height = gtk.HBox()
		hbox_width.pack_start(width_label, False, False, 10)
		hbox_width.pack_start(width, False, False, 0)
		hbox_height.pack_start(height_label, False, False, 10)
		hbox_height.pack_start(height, False, False, 0)
		vbox_right.pack_start(hbox_width, False, False, 0)
		vbox_right.pack_start(hbox_height, False, False, 0)
		hbox2 = gtk.HBox()
		hbox2.pack_start(gtk.Label(), expand=True)
		hbox2.pack_start(vbox_left, False, False, 0)
		hbox2.pack_start(vbox_right, False, False, 0)
		hbox2.pack_start(gtk.Label(), expand=True)
		dialog.vbox.pack_start(hbox, False, False, 0)
		dialog.vbox.pack_start(hbox2, False, False, 15)
		dialog.set_resizable(False)
		dialog.vbox.show_all()
		image.set_events(gtk.gdk.POINTER_MOTION_MASK | gtk.gdk.POINTER_MOTION_HINT_MASK | gtk.gdk.BUTTON_PRESS_MASK | gtk.gdk.BUTTON_MOTION_MASK | gtk.gdk.BUTTON_RELEASE_MASK)
		image.connect("expose-event", self.crop_image_expose_cb, crop_pixbuf, image_width, image_height)
		image.connect("motion_notify_event", self.crop_image_mouse_moved, image, 0, 0, x, y, width, height, image_width, image_height, width_adj, height_adj)
		image.connect("button_press_event", self.crop_image_button_press, image)
		image.connect("button_release_event", self.crop_image_button_release)
		self.x_changed = x.connect('value-changed', self.crop_value_changed, x, y, width, height, width_adj, height_adj, image_width, image_height, image, 0)
		self.y_changed = y.connect('value-changed', self.crop_value_changed, x, y, width, height, width_adj, height_adj, image_width, image_height, image, 1)
		self.width_changed = width.connect('value-changed', self.crop_value_changed, x, y, width, height, width_adj, height_adj, image_width, image_height, image, 2)
		self.height_changed = height.connect('value-changed', self.crop_value_changed, x, y, width, height, width_adj, height_adj, image_width, image_height, image, 3)
		image.realize()
		self.crop_rectangle = [0, 0]
		self.drawing_crop_rectangle = False
		self.update_rectangle = False
		self.rect = None
		response = dialog.run()
		if response == gtk.RESPONSE_ACCEPT:
			dialog.destroy()
			if self.rect != None:
				temp_pixbuf = gtk.gdk.Pixbuf(gtk.gdk.COLORSPACE_RGB, self.currimg_pixbuf_original.get_has_alpha(), 8, self.coords[2], self.coords[3])
				self.currimg_pixbuf_original.copy_area(self.coords[0], self.coords[1], self.coords[2], self.coords[3], temp_pixbuf, 0, 0)
				self.currimg_pixbuf_original = temp_pixbuf
				del temp_pixbuf
				gc.collect()
				self.load_new_image2(False, True, False, False)
				self.image_modified = True
		else:
			dialog.destroy()

	def crop_value_changed(self, currspinbox, x, y, width, height, width_adj, height_adj, image_width, image_height, image, type):
		if type == 0:   # X
			if x.get_value() + width.get_value() > self.currimg_pixbuf_original.get_width():
				width.handler_block(self.width_changed)
				width.set_value(self.currimg_pixbuf_original.get_width() - x.get_value())
				width.handler_unblock(self.width_changed)
		elif type == 1: # Y
			if y.get_value() + height.get_value() > self.currimg_pixbuf_original.get_height():
				height.handler_block(self.height_changed)
				height.set_value(self.currimg_pixbuf_original.get_height() - y.get_value())
				height.handler_unblock(self.height_changed)
		self.coords = [int(x.get_value()), int(y.get_value()), int(width.get_value()), int(height.get_value())]
		self.crop_rectangle[0] = int(round(float(self.coords[0])/self.currimg_pixbuf_original.get_width()*image_width, 0))
		self.crop_rectangle[1] = int(round(float(self.coords[1])/self.currimg_pixbuf_original.get_height()*image_height, 0))
		x2 = int(round(float(self.coords[2])/self.currimg_pixbuf_original.get_width()*image_width, 0)) + self.crop_rectangle[0]
		y2 = int(round(float(self.coords[3])/self.currimg_pixbuf_original.get_height()*image_height, 0)) + self.crop_rectangle[1]
		self.drawing_crop_rectangle = True
		self.update_rectangle = True
		self.crop_image_mouse_moved(None, None, image, x2, y2, x, y, width, height, image_width, image_height, width_adj, height_adj)
		self.update_rectangle = False
		self.drawing_crop_rectangle = False

	def crop_image_expose_cb(self, image, event, pixbuf, width, height):
		image.window.draw_pixbuf(None, pixbuf, 0, 0, 0, 0, width, height)

	def crop_image_mouse_moved(self, widget, event, image, x2, y2, x, y, width, height, image_width, image_height, width_adj, height_adj):
		if event != None:
			x2, y2, state = event.window.get_pointer()
		if self.drawing_crop_rectangle:
			if self.crop_rectangle != None or self.update_rectangle:
				gc = image.window.new_gc(function=gtk.gdk.INVERT)
				if self.rect != None:
					# Get rid of the previous drawn rectangle:
					image.window.draw_rectangle(gc, False, self.rect[0], self.rect[1], self.rect[2], self.rect[3])
				self.rect = [0, 0, 0, 0]
				if self.crop_rectangle[0] > x2:
					self.rect[0] = x2
					self.rect[2] = self.crop_rectangle[0]-x2
				else:
					self.rect[0] = self.crop_rectangle[0]
					self.rect[2] = x2-self.crop_rectangle[0]
				if self.crop_rectangle[1] > y2:
					self.rect[1] = y2
					self.rect[3] = self.crop_rectangle[1]-y2
				else:
					self.rect[1] = self.crop_rectangle[1]
					self.rect[3] = y2-self.crop_rectangle[1]
				image.window.draw_rectangle(gc, False, self.rect[0], self.rect[1], self.rect[2], self.rect[3])
				# Convert the rectangle coordinates of the current image
				# to coordinates of pixbuf_original
				if self.rect[0] < 0:
					self.rect[2] = self.rect[2] + self.rect[0]
					self.rect[0] = 0
				if self.rect[1] < 0:
					self.rect[3] = self.rect[3] + self.rect[1]
					self.rect[1] = 0
				if event != None:
					self.coords = [0,0,0,0]
					self.coords[0] = int(round(float(self.rect[0])/image_width*self.currimg_pixbuf_original.get_width(), 0))
					self.coords[1] = int(round(float(self.rect[1])/image_height*self.currimg_pixbuf_original.get_height(), 0))
					self.coords[2] = int(round(float(self.rect[2])/image_width*self.currimg_pixbuf_original.get_width(), 0))
					self.coords[3] = int(round(float(self.rect[3])/image_height*self.currimg_pixbuf_original.get_height(), 0))
					if self.coords[0] + self.coords[2] > self.currimg_pixbuf_original.get_width():
						self.coords[2] = self.currimg_pixbuf_original.get_width() - self.coords[0]
					if self.coords[1] + self.coords[3] > self.currimg_pixbuf_original.get_height():
						self.coords[3] = self.currimg_pixbuf_original.get_height() - self.coords[1]
				x.handler_block(self.x_changed)
				y.handler_block(self.y_changed)
				width.handler_block(self.width_changed)
				height.handler_block(self.height_changed)
				x.set_value(self.coords[0])
				y.set_value(self.coords[1])
				width.set_value(self.coords[2])
				height.set_value(self.coords[3])
				x.handler_unblock(self.x_changed)
				y.handler_unblock(self.y_changed)
				width_adj.set_property('upper', self.currimg_pixbuf_original.get_width() - self.coords[0])
				height_adj.set_property('upper', self.currimg_pixbuf_original.get_height() - self.coords[1])
				width.handler_unblock(self.width_changed)
				height.handler_unblock(self.height_changed)

	def crop_image_button_press(self, widget, event, image):
		x, y, state = event.window.get_pointer()
		if (state & gtk.gdk.BUTTON1_MASK):
			self.drawing_crop_rectangle = True
			self.crop_rectangle = [x, y]
			gc = image.window.new_gc(function=gtk.gdk.INVERT)
			if self.rect != None:
				# Get rid of the previous drawn rectangle:
				image.window.draw_rectangle(gc, False, self.rect[0], self.rect[1], self.rect[2], self.rect[3])
				self.rect = None

	def crop_image_button_release(self, widget, event):
		x, y, state = event.window.get_pointer()
		if not (state & gtk.gdk.BUTTON1_MASK):
			self.drawing_crop_rectangle = False

	def saturation(self, action):
		dialog = gtk.Dialog(_("Saturation"), self.window, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT))
		resizebutton = dialog.add_button(_("_Saturate"), gtk.RESPONSE_ACCEPT)
		resizeimage = gtk.Image()
		resizeimage.set_from_stock(gtk.STOCK_OK, gtk.ICON_SIZE_BUTTON)
		resizebutton.set_image(resizeimage)
		scale = gtk.HScale()
		scale.set_draw_value(False)
		scale.set_update_policy(gtk.UPDATE_DISCONTINUOUS)
		scale.set_range(0, 2)
		scale.set_increments(0.1, 0.5)
		scale.set_value(1)
		scale.connect('value-changed', self.saturation_preview)
		label = gtk.Label(_("Saturation level:"))
		label.set_alignment(0, 0.5)
		hbox1 = gtk.HBox()
		hbox1.pack_start(label, True, True, 10)
		hbox2 = gtk.HBox()
		hbox2.pack_start(scale, True, True, 20)
		dialog.vbox.pack_start(gtk.Label(" "))
		dialog.vbox.pack_start(hbox1, False)
		dialog.vbox.pack_start(hbox2, True, True, 10)
		dialog.vbox.pack_start(gtk.Label(" "))
		dialog.set_default_response(gtk.RESPONSE_ACCEPT)
		dialog.vbox.show_all()
		response = dialog.run()
		if response == gtk.RESPONSE_ACCEPT:
			self.currimg_pixbuf_original.saturate_and_pixelate(self.currimg_pixbuf_original, scale.get_value(), False)
			self.currimg_pixbuf.saturate_and_pixelate(self.currimg_pixbuf, scale.get_value(), False)
			self.imageview.set_from_pixbuf(self.currimg_pixbuf)
			self.image_modified = True
			dialog.destroy()
		else:
			self.imageview.set_from_pixbuf(self.currimg_pixbuf)
			dialog.destroy()

	def saturation_preview(self, range):
		while gtk.events_pending():
			gtk.main_iteration()
		try:
			bak = self.currimg_pixbuf.copy()
			self.currimg_pixbuf.saturate_and_pixelate(self.currimg_pixbuf, range.get_value(), False)
			self.imageview.set_from_pixbuf(self.currimg_pixbuf)
			self.currimg_pixbuf = bak.copy()
			del bak
		except:
			pass
		gc.collect()

	def resize_image(self, action):
		dialog = gtk.Dialog(_("Resize Image"), self.window, gtk.DIALOG_MODAL, (gtk.STOCK_CANCEL, gtk.RESPONSE_REJECT))
		resizebutton = dialog.add_button(_("_Resize"), gtk.RESPONSE_ACCEPT)
		resizeimage = gtk.Image()
		resizeimage.set_from_stock(gtk.STOCK_OK, gtk.ICON_SIZE_BUTTON)
		resizebutton.set_image(resizeimage)
		hbox_width = gtk.HBox()
		width_adj = gtk.Adjustment(self.currimg_pixbuf_original.get_width(), 1, 100000000000, 1, 10, 0)
		width = gtk.SpinButton(width_adj, 0, 0)
		width.set_numeric(True)
		width.set_update_policy(gtk.UPDATE_IF_VALID)
		width.set_wrap(False)
		width_label = gtk.Label(_("Width:"))
		width_label.set_alignment(0, 0.7)
		hbox_width.pack_start(width_label, False, False, 10)
		hbox_width.pack_start(width, False, False, 0)
		hbox_width.pack_start(gtk.Label(_("pixels")), False, False, 10)
		hbox_height = gtk.HBox()
		height_adj = gtk.Adjustment(self.currimg_pixbuf_original.get_height(), 1, 100000000000, 1, 10, 0)
		height = gtk.SpinButton(height_adj, 0, 0)
		height.set_numeric(True)
		height.set_update_policy(gtk.UPDATE_IF_VALID)
		height.set_wrap(False)
		height_label = gtk.Label(_("Height:"))
		width_label.set_size_request(height_label.size_request()[0], -1)
		height_label.set_alignment(0, 0.7)
		hbox_height.pack_start(height_label, False, False, 10)
		hbox_height.pack_start(height, False, False, 0)
		hbox_height.pack_start(gtk.Label(_("pixels")), False, False, 10)
		hbox_aspect = gtk.HBox()
		aspect_checkbox = gtk.CheckButton(_("Preserve aspect ratio"))
		aspect_checkbox.set_active(self.preserve_aspect)
		hbox_aspect.pack_start(aspect_checkbox, False, False, 10)
		vbox = gtk.VBox()
		vbox.pack_start(gtk.Label(), False, False, 0)
		vbox.pack_start(hbox_width, False, False, 0)
		vbox.pack_start(hbox_height, False, False, 0)
		vbox.pack_start(gtk.Label(), False, False, 0)
		vbox.pack_start(hbox_aspect, False, False, 0)
		vbox.pack_start(gtk.Label(), False, False, 0)
		hbox_total = gtk.HBox()
		animtest = gtk.gdk.PixbufAnimation(self.currimg_name)
		if animtest.is_static_image():
			pixbuf, image_width, image_height = self.get_pixbuf_of_size(self.currimg_pixbuf_original, 96, self.zoom_quality)
		else:
			pixbuf, image_width, image_height = self.get_pixbuf_of_size(animtest.get_static_image(), 96, self.zoom_quality)
		image = gtk.Image()
		image.set_from_pixbuf(self.pixbuf_add_border(pixbuf))
		hbox_total.pack_start(image, False, False, 10)
		hbox_total.pack_start(vbox, False, False, 10)
		dialog.vbox.pack_start(hbox_total, False, False, 0)
		width.connect('value-changed', self.preserve_image_aspect, "width", height)
		height.connect('value-changed', self.preserve_image_aspect, "height", width)
		aspect_checkbox.connect('toggled', self.aspect_ratio_toggled, width, height)
		dialog.set_default_response(gtk.RESPONSE_ACCEPT)
		dialog.vbox.show_all()
		response = dialog.run()
		if response == gtk.RESPONSE_ACCEPT:
			pixelheight = height.get_value_as_int()
			pixelwidth = width.get_value_as_int()
			dialog.destroy()
			self.currimg_pixbuf_original = self.currimg_pixbuf_original.scale_simple(pixelwidth, pixelheight, self.zoom_quality)
			self.load_new_image2(False, True, False, False)
			self.image_modified = True
		else:
			dialog.destroy()

	def aspect_ratio_toggled(self, togglebutton, width, height):
		self.preserve_aspect = togglebutton.get_active()
		if self.preserve_aspect:
			# Set height based on width and aspect ratio
			target_value = float(width.get_value_as_int())/self.currimg_pixbuf_original.get_width()
			target_value = int(target_value * self.currimg_pixbuf_original.get_height())
			self.ignore_preserve_aspect_callback = True
			height.set_value(target_value)
			self.ignore_preserve_aspect_callback = False

	def preserve_image_aspect(self, currspinbox, type, otherspinbox):
		if not self.preserve_aspect:
			return
		if self.ignore_preserve_aspect_callback:
			return
		if type == "width":
			target_value = float(currspinbox.get_value_as_int())/self.currimg_pixbuf_original.get_width()
			target_value = int(target_value * self.currimg_pixbuf_original.get_height())
		else:
			target_value = float(currspinbox.get_value_as_int())/self.currimg_pixbuf_original.get_height()
			target_value = int(target_value * self.currimg_pixbuf_original.get_width())
		self.ignore_preserve_aspect_callback = True
		otherspinbox.set_value(target_value)
		self.ignore_preserve_aspect_callback = False

	def goto_prev_image(self, action):
		self.goto_image("PREV", action)

	def goto_next_image(self, action):
		self.goto_image("NEXT", action)

	def goto_random_image(self, action):
		self.goto_image("RANDOM", action)

	def goto_first_image(self, action):
		self.goto_image("FIRST", action)

	def goto_last_image(self, action):
		self.goto_image("LAST", action)
		
	def goto_image(self, location, action):
		# location can be "LAST", "FIRST", "NEXT", "PREV", "RANDOM", or a number
		if self.slideshow_mode and action != "ss":
			gobject.source_remove(self.timer_delay)
		if ((location=="PREV" or location=="NEXT" or location=="RANDOM") and len(self.image_list) > 1) or (location=="FIRST" and (len(self.image_list) > 1 and self.curr_img_in_list != 0)) or (location=="LAST" and (len(self.image_list) > 1 and self.curr_img_in_list != len(self.image_list)-1)) or valid_int(location):
			self.load_new_image_stop_now()
			cancel = self.autosave_image()
			if cancel:
				return
			check_wrap = False
			if location != "RANDOM":
				self.randomlist = []
			if location == "FIRST":
				self.curr_img_in_list = 0
			elif location == "RANDOM":
				if self.randomlist == []:
					self.reinitialize_randomlist()
				else:
					# check if we have seen every image; if so, reinitialize array and repeat:
					all_items_are_true = True
					for item in self.randomlist:
						if not item:
							all_items_are_true = False
					if all_items_are_true:
						if not self.slideshow_mode or (self.slideshow_mode and self.listwrap_mode == 1):
							self.reinitialize_randomlist()
						else:
							check_wrap = True
			elif location == "LAST":
				self.curr_img_in_list = len(self.image_list)-1
			elif location == "PREV":
				if self.curr_img_in_list > 0:
					self.curr_img_in_list -= 1
				else:
					check_wrap = True
			elif location == "NEXT":
				if self.curr_img_in_list < len(self.image_list) - 1:
					self.curr_img_in_list += 1
				else:
					check_wrap = True
			if check_wrap:
				if self.listwrap_mode == 0:
					if location == "NEXT":
						if self.slideshow_mode:
							self.toggle_slideshow(None)
					return
				elif (location == "PREV" or location == "NEXT") and self.listwrap_mode == 1:
					if location == "PREV":
						self.curr_img_in_list = len(self.image_list) - 1
					elif location == "NEXT":
						self.curr_img_in_list = 0
				else:
					if self.curr_img_in_list != self.loaded_img_in_list:
						# Ensure that the user is looking at the correct "last" image before
						# they are asked the wrap question:
						if location == "PREV":
							self.load_new_image(True, False, True, True, True, True)
						else:
							self.load_new_image(False, False, True, True, True, True)
						self.set_go_navigation_sensitivities(False)
						self.thumbpane_select(self.curr_img_in_list)
					if self.fullscreen_mode:
						self.change_cursor(None)
					if location == "PREV":
						dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT, gtk.MESSAGE_QUESTION, gtk.BUTTONS_YES_NO, _("You are viewing the first image in the list. Wrap around to the last image?"))
					elif location == "NEXT":
						dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT, gtk.MESSAGE_QUESTION, gtk.BUTTONS_YES_NO, _("You are viewing the last image in the list. Wrap around to the first image?"))
					elif location == "RANDOM":
						dialog = gtk.MessageDialog(self.window, gtk.DIALOG_MODAL | gtk.DIALOG_DESTROY_WITH_PARENT, gtk.MESSAGE_QUESTION, gtk.BUTTONS_YES_NO, _("All images have been viewed. Would you like to cycle through the images again?"))
					dialog.set_title(_("Wrap?"))
					dialog.label.set_property('can-focus', False)
					dialog.set_default_response(gtk.RESPONSE_YES)
					self.user_prompt_visible = True
					response = dialog.run()
					if response == gtk.RESPONSE_YES:
						if location == "PREV":
							self.curr_img_in_list = len(self.image_list)-1
						elif location == "NEXT":
							self.curr_img_in_list = 0
						elif location == "RANDOM":
							self.reinitialize_randomlist()
						dialog.destroy()
						self.user_prompt_visible = False
						if self.fullscreen_mode:
							self.hide_cursor
					else:
						dialog.destroy()
						self.user_prompt_visible = False
						if self.fullscreen_mode:
							self.hide_cursor
						else:
							self.change_cursor(None)
						if self.slideshow_mode:
							self.toggle_slideshow(None)
						return
			if location == "RANDOM":
				# Find random image that hasn't already been chosen:
				j = random.randint(0, len(self.image_list)-1)
				while self.randomlist[j]:
					j = random.randint(0, len(self.image_list)-1)
				self.curr_img_in_list = j
				self.randomlist[j] = True
				self.currimg_name = str(self.image_list[self.curr_img_in_list])
			if valid_int(location):
				prev_img = self.curr_img_in_list
				self.curr_img_in_list = int(location)
			if not self.fullscreen_mode and (not self.slideshow_mode or (self.slideshow_mode and action != "ss")):
				self.change_cursor(gtk.gdk.Cursor(gtk.gdk.WATCH))
			if location == "PREV" or (valid_int(location) and int(location) == prev_img-1):
				self.load_when_idle = gobject.idle_add(self.load_new_image, True, False, True, True, True, True)
			else:
				self.load_when_idle = gobject.idle_add(self.load_new_image, False, False, True, True, True, True)
			self.set_go_navigation_sensitivities(False)
			if self.slideshow_mode:
				if self.curr_slideshow_random:
					self.timer_delay = gobject.timeout_add(int(self.curr_slideshow_delay*1000), self.goto_random_image, "ss")
				else:
					self.timer_delay = gobject.timeout_add(int(self.curr_slideshow_delay*1000), self.goto_next_image, "ss")
			gobject.idle_add(self.thumbpane_select, self.curr_img_in_list)
		
	def set_go_navigation_sensitivities(self, skip_initial_check):
		# setting skip_image_list_check to True is useful when calling from
		# expand_filelist_and_load_image() for example, as self.image_list has not
		# yet fully populated
		if (not self.image_loaded or len(self.image_list) == 1) and not skip_initial_check:
			self.set_previous_image_sensitivities(False)
			self.set_first_image_sensitivities(False)
			self.set_next_image_sensitivities(False)
			self.set_last_image_sensitivities(False)
			self.set_random_image_sensitivities(False)
		elif self.curr_img_in_list == 0:
			if self.listwrap_mode == 0:
				self.set_previous_image_sensitivities(False)
			else:
				self.set_previous_image_sensitivities(True)
			self.set_first_image_sensitivities(False)
			self.set_next_image_sensitivities(True)
			self.set_last_image_sensitivities(True)
			self.set_random_image_sensitivities(True)
		elif self.curr_img_in_list == len(self.image_list)-1:
			self.set_previous_image_sensitivities(True)
			self.set_first_image_sensitivities(True)
			if self.listwrap_mode == 0:
				self.set_next_image_sensitivities(False)
			else:
				self.set_next_image_sensitivities(True)
			self.set_last_image_sensitivities(False)
			self.set_random_image_sensitivities(True)
		else:
			self.set_previous_image_sensitivities(True)
			self.set_first_image_sensitivities(True)
			self.set_next_image_sensitivities(True)
			self.set_last_image_sensitivities(True)
			self.set_random_image_sensitivities(True)

	def reinitialize_randomlist(self):
		self.randomlist = []
		for i in range(len(self.image_list)):
			self.randomlist.append(False)
		self.randomlist[self.curr_img_in_list] = True

	def image_load_failed(self, reset_cursor, filename=""):
		# If a filename is provided, use it for display:
		if len(filename) == 0:
			self.currimg_name = str(self.image_list[self.curr_img_in_list])
		else:
			self.currmg_name = filename
		if self.verbose and self.currimg_name != "":
			print _("Loading: %s") % self.currimg_name
		self.update_title()
		self.put_error_image_to_window()
		self.image_loaded = False
		self.currimg_pixbuf_original = None
		if reset_cursor:
			if not self.fullscreen_mode:
				self.change_cursor(None)

	def load_new_image_stop_now(self):
		try:
			gobject.source_remove(self.load_when_idle)
		except:
			pass
		try:
			gobject.source_remove(self.preload_when_idle)
		except:
			pass
		try:
			gobject.source_remove(self.preload_when_idle2)
		except:
			pass

	def load_new_image(self, check_prev_last, use_current_pixbuf_original, reset_cursor, perform_onload_action, preload_next_image_after, preload_prev_image_after):
		try:
			self.load_new_image2(check_prev_last, use_current_pixbuf_original, reset_cursor, perform_onload_action)
		except:
			self.image_load_failed(True)
		if preload_next_image_after:
			self.preload_when_idle = gobject.idle_add(self.preload_next_image, False)
		if preload_prev_image_after:
			self.preload_when_idle2 = gobject.idle_add(self.preload_prev_image, False)

	def check_preloadimg_prev_for_existing(self, prev_index, reset_preloadimg_prev_in_list):
		# Determines if preloadimg_prev needs to be updated; if so,
		# checks if the image is already stored in self.currimg
		# or self.preloadimg_next and can be reused.
		reset_preloadimg_prev_in_list = False
		if prev_index != self.preloadimg_prev_in_list and prev_index != -1:
			# Need to update preloadimg_prev:
			if prev_index == self.loaded_img_in_list and not self.image_modified and not self.image_zoomed:
				self.preloadimg_prev_in_list = self.loaded_img_in_list
				self.preloadimg_prev_name = self.currimg_name
				self.preloadimg_prev_width = self.currimg_width
				self.preloadimg_prev_height = self.currimg_height
				self.preloadimg_prev_pixbuf = self.currimg_pixbuf
				self.preloadimg_prev_pixbuf_original = self.currimg_pixbuf_original
				self.preloadimg_prev_zoomratio = self.currimg_zoomratio
				self.preloadimg_prev_is_animation = self.currimg_is_animation
			elif prev_index == self.preloadimg_next_in_list:
				self.preloadimg_prev_in_list = self.preloadimg_next_in_list
				self.preloadimg_prev_name = self.preloadimg_next_name
				self.preloadimg_prev_width = self.preloadimg_next_width
				self.preloadimg_prev_height = self.preloadimg_next_height
				self.preloadimg_prev_pixbuf = self.preloadimg_next_pixbuf
				self.preloadimg_prev_pixbuf_original = self.preloadimg_next_pixbuf_original
				self.preloadimg_prev_zoomratio = self.preloadimg_next_zoomratio
				self.preloadimg_prev_is_animation = self.preloadimg_next_is_animation
			else:
				reset_preloadimg_prev_in_list = True
		elif prev_index == -1:
			reset_preloadimg_prev_in_list = True

	def check_preloadimg_next_for_existing(self, next_index, reset_preloadimg_next_in_list):
		# Determines if preloadimg_next needs to be updated; if so,
		# checks if the image is already stored in self.currimg
		# or self.preloadimg_prev and can be reused.
		reset_preloadimg_next_in_list = False
		if next_index != self.preloadimg_next_in_list and next_index != -1:
			# Need to update preloadimg_next:
			if next_index == self.loaded_img_in_list and not self.image_modified and not self.image_zoomed:
				self.preloadimg_next_in_list = self.loaded_img_in_list
				self.preloadimg_next_name = self.currimg_name
				self.preloadimg_next_width = self.currimg_width
				self.preloadimg_next_height = self.currimg_height
				self.preloadimg_next_pixbuf = self.currimg_pixbuf
				self.preloadimg_next_pixbuf_original = self.currimg_pixbuf_original
				self.preloadimg_next_zoomratio = self.currimg_zoomratio
				self.preloadimg_next_is_animation = self.currimg_is_animation
			elif next_index == self.preloadimg_prev_in_list:
				self.preloadimg_next_in_list = self.preloadimg_prev_in_list
				self.preloadimg_next_name = self.preloadimg_prev_name
				self.preloadimg_next_width = self.preloadimg_prev_width
				self.preloadimg_next_height = self.preloadimg_prev_height
				self.preloadimg_next_pixbuf = self.preloadimg_prev_pixbuf
				self.preloadimg_next_pixbuf_original = self.preloadimg_prev_pixbuf_original
				self.preloadimg_next_zoomratio = self.preloadimg_prev_zoomratio
				self.preloadimg_next_is_animation = self.preloadimg_prev_is_animation
			else:
				reset_preloadimg_next_in_list = True
		elif next_index == -1:
			reset_preloadimg_next_in_list = True

	def check_currimg_for_existing(self):
		# Determines if currimg needs to be updated; if so,
		# checks if the image is already stored in self.preloadimg_next
		# or self.preloadimg_prev and can be reused (the whole point of
		# preloading!)
		used_prev = False
		used_next = False
		if self.curr_img_in_list != self.loaded_img_in_list:
			# Need to update currimg:
			if self.curr_img_in_list == self.preloadimg_prev_in_list:
				# Set preload_prev_image as current image
				self.currimg_name = self.preloadimg_prev_name
				self.currimg_width = self.preloadimg_prev_width
				self.currimg_height = self.preloadimg_prev_height
				self.currimg_pixbuf = self.preloadimg_prev_pixbuf
				self.currimg_pixbuf_original = self.preloadimg_prev_pixbuf_original
				self.currimg_zoomratio = self.preloadimg_prev_zoomratio
				self.currimg_is_animation = self.preloadimg_prev_is_animation
				used_prev = True
				if self.verbose and self.currimg_name != "":
					print _("Loading: %s") % self.currimg_name
				self.put_zoom_image_to_window(True)
				if not self.currimg_is_animation:
					self.set_image_sensitivities(True)
				else:
					self.set_image_sensitivities(False)
			elif self.curr_img_in_list == self.preloadimg_next_in_list:
				# Use preload_next_image as current image
				self.currimg_name = self.preloadimg_next_name
				self.currimg_width = self.preloadimg_next_width
				self.currimg_height = self.preloadimg_next_height
				self.currimg_pixbuf = self.preloadimg_next_pixbuf
				self.currimg_pixbuf_original = self.preloadimg_next_pixbuf_original
				self.currimg_zoomratio = self.preloadimg_next_zoomratio
				self.currimg_is_animation = self.preloadimg_next_is_animation
				used_next = True
				if self.verbose and self.currimg_name != "":
					print _("Loading: %s") % self.currimg_name
				self.put_zoom_image_to_window(True)
				if not self.currimg_is_animation:
					self.set_image_sensitivities(True)
				else:
					self.set_image_sensitivities(False)
		return used_prev, used_next

	def load_new_image2(self, check_prev_last, use_current_pixbuf_original, reset_cursor, perform_onload_action, skip_recentfiles=False):
		# check_prev_last is used to determine if we should check whether
		# preloadimg_prev can be reused last. This should really only
		# be done if the user just clicked the previous image button in
		# order to reduce the number of image loads.
		# If use_current_pixbuf_original == True, do not reload the
		# self.currimg_pixbuf_original from the file; instead, use the existing
		# one. This is only currently useful for resizing images.
		# Determine the indices in the self.image_list array for the
		# previous and next preload images.
		next_index = self.curr_img_in_list + 1
		if next_index > len(self.image_list)-1:
			if self.listwrap_mode == 0:
				next_index = -1
			else:
				next_index = 0
		prev_index = self.curr_img_in_list - 1
		if prev_index < 0:
			if self.listwrap_mode == 0:
				prev_index = -1
			else:
				prev_index = len(self.image_list)-1
		if self.preloading_images:
			reset_preloadimg_next_in_list = False
			reset_preloadimg_prev_in_list = False
			if check_prev_last:
				self.check_preloadimg_next_for_existing(next_index, reset_preloadimg_next_in_list)
			else:
				self.check_preloadimg_prev_for_existing(prev_index, reset_preloadimg_prev_in_list)
		used_prev, used_next = self.check_currimg_for_existing()
		if self.preloading_images:
			if check_prev_last:
				self.check_preloadimg_prev_for_existing(prev_index, reset_preloadimg_prev_in_list)
			else:
				self.check_preloadimg_next_for_existing(next_index, reset_preloadimg_next_in_list)
			if reset_preloadimg_prev_in_list:
				self.preloadimg_prev_in_list = -1
			if reset_preloadimg_next_in_list:
				self.preloadimg_next_in_list = -1
		if used_prev or used_next:
			# If we used a preload image, set the correct boolean variables
			if self.open_mode == self.open_mode_smart or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_smart):
				self.last_image_action_was_fit = True
				self.last_image_action_was_smart_fit = True
			elif self.open_mode == self.open_mode_fit or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_fit):
				self.last_image_action_was_fit = True
				self.last_image_action_was_smart_fit = False
			elif self.open_mode == self.open_mode_1to1 or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_1to1):
				self.last_image_action_was_fit = False
			self.currimg_name = str(self.image_list[self.curr_img_in_list])
		else:
			# Need to load the current image
			self.currimg_pixbuf = None
			self.currimg_zoomratio = 1
			self.currimg_name = str(self.image_list[self.curr_img_in_list])
			if self.verbose and self.currimg_name != "":
				print _("Loading: %s") % self.currimg_name
			animtest = gtk.gdk.PixbufAnimation(self.currimg_name)
			if animtest.is_static_image() or (use_current_pixbuf_original and not self.currimg_is_animation):
				self.currimg_is_animation = False
				if not use_current_pixbuf_original:
					self.currimg_pixbuf_original = animtest.get_static_image()
				self.set_image_sensitivities(True)
				if self.open_mode == self.open_mode_smart or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_smart):
					self.zoom_to_fit_or_1_to_1(None, False, False)
				elif self.open_mode == self.open_mode_fit or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_fit):
					self.zoom_to_fit_window(None, False, False)
				elif self.open_mode == self.open_mode_1to1 or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_1to1):
					self.zoom_1_to_1(None, False, False)
			else:
				self.currimg_is_animation = True
				if not use_current_pixbuf_original:
					self.currimg_pixbuf_original = animtest
				self.zoom_1_to_1(None, False, False)
				self.set_image_sensitivities(False)
		if self.onload_cmd != None and perform_onload_action:
			self.parse_action_command(self.onload_cmd, False)
		self.update_statusbar()
		self.update_title()
		self.image_loaded = True
		self.image_modified = False
		self.image_zoomed = False
		self.set_slideshow_sensitivities()
		if not skip_recentfiles:
			self.register_file_with_recent_docs(self.currimg_name)
		if reset_cursor:
			if not self.fullscreen_mode:
				self.change_cursor(None)

	def preload_next_image(self, use_existing_image):
		try:
			if self.preloading_images and len(self.image_list) > 1:
				if not use_existing_image:
					next_index = self.curr_img_in_list + 1
					if next_index > len(self.image_list)-1:
						if self.listwrap_mode == 0:
							self.preloadimg_next_in_list == -1
							return
						else:
							next_index = 0
					if next_index == self.preloadimg_next_in_list:
						return
					self.preloadimg_next_in_list = next_index
					self.preloadimg_next_name = str(self.image_list[next_index])
					pre_animtest = gtk.gdk.PixbufAnimation(self.preloadimg_next_name)
					if pre_animtest.is_static_image():
						self.preloadimg_next_is_animation = False
						self.preloadimg_next_pixbuf_original = pre_animtest.get_static_image()
					else:
						self.preloadimg_next_is_animation = True
						self.preloadimg_next_pixbuf_original = pre_animtest
				if self.preloadimg_next_in_list == -1:
					return
				# Determine self.preloadimg_next_zoomratio
				if self.open_mode == self.open_mode_smart or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_smart):
					self.zoom_to_fit_or_1_to_1(None, True, False)
				elif self.open_mode == self.open_mode_fit or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_fit):
					self.zoom_to_fit_window(None, True, False)
				elif self.open_mode == self.open_mode_1to1 or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_1to1):
					self.zoom_1_to_1(None, True, False)
				# Always start with the original image to preserve quality!
				# Calculate image size:
				self.preloadimg_next_width = int(self.preloadimg_next_pixbuf_original.get_width() * self.preloadimg_next_zoomratio)
				self.preloadimg_next_height = int(self.preloadimg_next_pixbuf_original.get_height() * self.preloadimg_next_zoomratio)
				if not self.preloadimg_next_is_animation:
					# Scale image:
					if not self.preloadimg_next_pixbuf_original.get_has_alpha():
						self.preloadimg_next_pixbuf = self.preloadimg_next_pixbuf_original.scale_simple(self.preloadimg_next_width, self.preloadimg_next_height, self.zoom_quality)
					else:
						colormap = self.imageview.get_colormap()
						light_grey = colormap.alloc_color('#666666', True, True)
						dark_grey = colormap.alloc_color('#999999', True, True)
						self.preloadimg_next_pixbuf = self.preloadimg_next_pixbuf_original.composite_color_simple(self.preloadimg_next_width, self.preloadimg_next_height, self.zoom_quality, 255, 8, light_grey.pixel, dark_grey.pixel)
				else:
					self.preloadimg_next_pixbuf = self.preloadimg_next_pixbuf_original
				gc.collect()
				if self.verbose:
					print _("Preloading: %s") % self.preloadimg_next_name
		except:
			self.preloadimg_next_in_list = -1

	def preload_prev_image(self, use_existing_image):
		try:
			if self.preloading_images and len(self.image_list) > 1:
				if not use_existing_image:
					prev_index = self.curr_img_in_list - 1
					if prev_index < 0:
						if self.listwrap_mode == 0:
							self.preloadimg_prev_in_list == -1
							return
						else:
							prev_index = len(self.image_list)-1
					if prev_index == self.preloadimg_prev_in_list:
						return
					self.preloadimg_prev_in_list = prev_index
					self.preloadimg_prev_name = str(self.image_list[prev_index])
					pre_animtest = gtk.gdk.PixbufAnimation(self.preloadimg_prev_name)
					if pre_animtest.is_static_image():
						self.preloadimg_prev_is_animation = False
						self.preloadimg_prev_pixbuf_original = pre_animtest.get_static_image()
					else:
						self.preloadimg_prev_is_animation = True
						self.preloadimg_prev_pixbuf_original = pre_animtest
				if self.preloadimg_prev_in_list == -1:
					return
				# Determine self.preloadimg_prev_zoomratio
				if self.open_mode == self.open_mode_smart or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_smart):
					self.zoom_to_fit_or_1_to_1(None, False, True)
				elif self.open_mode == self.open_mode_fit or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_fit):
					self.zoom_to_fit_window(None, False, True)
				elif self.open_mode == self.open_mode_1to1 or (self.open_mode == self.open_mode_last and self.last_mode == self.open_mode_1to1):
					self.zoom_1_to_1(None, False, True)
				# Always start with the original image to preserve quality!
				# Calculate image size:
				self.preloadimg_prev_width = int(self.preloadimg_prev_pixbuf_original.get_width() * self.preloadimg_prev_zoomratio)
				self.preloadimg_prev_height = int(self.preloadimg_prev_pixbuf_original.get_height() * self.preloadimg_prev_zoomratio)
				if not self.preloadimg_prev_is_animation:
					# Scale image:
					if not self.preloadimg_prev_pixbuf_original.get_has_alpha():
						self.preloadimg_prev_pixbuf = self.preloadimg_prev_pixbuf_original.scale_simple(self.preloadimg_prev_width, self.preloadimg_prev_height, self.zoom_quality)
					else:
						colormap = self.imageview.get_colormap()
						light_grey = colormap.alloc_color('#666666', True, True)
						dark_grey = colormap.alloc_color('#999999', True, True)
						self.preloadimg_prev_pixbuf = self.preloadimg_prev_pixbuf_original.composite_color_simple(self.preloadimg_prev_width, self.preloadimg_prev_height, self.zoom_quality, 255, 8, light_grey.pixel, dark_grey.pixel)
				else:
					self.preloadimg_prev_pixbuf = self.preloadimg_prev_pixbuf_original
				gc.collect()
				if self.verbose:
					print _("Preloading: %s") % self.preloadimg_prev_name
		except:
			self.preloadimg_prev_in_list = -1

	def change_cursor(self, type):
		for i in gtk.gdk.window_get_toplevels():
			if i.get_window_type() != gtk.gdk.WINDOW_TEMP and i.get_window_type() != gtk.gdk.WINDOW_CHILD:
				i.set_cursor(type)
		self.layout.window.set_cursor(type)

	def expand_filelist_and_load_image(self, inputlist):
		# Takes the current list (i.e. ["pic.jpg", "pic2.gif", "../images"]) and
		# expands it into a list of all pictures found
		self.thumblist.clear()
		first_image_loaded_successfully = False
		self.images_found = 0
		self.stop_now = True # Make sure that any previous search process is stopped
		self.change_cursor(gtk.gdk.Cursor(gtk.gdk.WATCH))
		# Reset preload images:
		self.preloadimg_next_in_list = -1
		self.preloadimg_prev_in_list = -1
		# If any directories were passed, display "Searching..." in statusbar:
		self.searching_for_images = False
		for item in inputlist:
			if os.path.isdir(item):
				self.searching_for_images = True
				self.update_statusbar()
		if not self.closing_app:
			while gtk.events_pending():
				gtk.main_iteration()
		first_image = ""
		first_image_found = False
		first_image_loaded = False
		second_image = ""
		second_image_found = False
		second_image_preloaded = False
		self.randomlist = []
		folderlist = []
		self.image_list = []
		self.curr_img_in_list = 0
		go_buttons_enabled = False
		self.set_go_sensitivities(False)
		# Clean up list (remove preceding "file://" or "file:" and trailing "/")
		for itemnum in range(len(inputlist)):
			# Strip off preceding file..
			if inputlist[itemnum].startswith('file://'):
				inputlist[itemnum] = inputlist[itemnum][7:]
			elif inputlist[itemnum].startswith('file:'):
				inputlist[itemnum] = inputlist[itemnum][5:]
			# Strip off trailing "/" if it exists:
			if inputlist[itemnum][len(inputlist[itemnum])-1] == "/":
				inputlist[itemnum] = inputlist[itemnum][:(len(inputlist[itemnum])-1)]
			if not (inputlist[itemnum].startswith('http://') or inputlist[itemnum].startswith('ftp://')):
				inputlist[itemnum] = os.path.abspath(inputlist[itemnum])
			else:
				try:
					# Remote file. Save as /tmp/mirage-<random>/filename.ext
					tmpdir = tempfile.mkdtemp(prefix="mirage-") + "/"
					tmpfile = tmpdir + os.path.basename(inputlist[itemnum])
					socket.setdefaulttimeout(5)
					urllib.urlretrieve(inputlist[itemnum], tmpfile)
					inputlist[itemnum] = tmpfile
				except:
					pass
		# Remove hidden files from list:
		if not self.open_hidden_files:
			tmplist = []
			for item in inputlist:
				if os.path.basename(item)[0] != '.':
					tmplist.append(item)
				elif self.verbose:
					print _("Skipping: %s") % item
			inputlist = tmplist
			if len(inputlist) == 0:
				# All files/dirs were hidden, exit..
				self.currimg_name = ""
				self.searching_for_images = False
				self.set_go_navigation_sensitivities(False)
				self.set_slideshow_sensitivities()
				if not self.closing_app:
					self.change_cursor(None)
				self.recursive = False
				self.put_error_image_to_window()
				self.update_title()
				return
		init_image = os.path.abspath(inputlist[0])
		self.stop_now = False
		# If open all images in dir...
		if self.open_all_images:
			temp = inputlist
			inputlist = []
			for item in temp:
				if os.path.isfile(item):
					itempath = os.path.dirname(os.path.abspath(item))
					temp = self.recursive
					self.recursive = False
					self.stop_now = False
					self.expand_directory(itempath, False, go_buttons_enabled, False, False)
					self.recursive = temp
				else:
					inputlist.append(item)
			for item in self.image_list:
				inputlist.append(item)
				if first_image_found and not second_image_found:
					second_image_found = True
					second_image = item
					second_image_came_from_dir = False
				if item == init_image:
					first_image_found = True
					first_image = item
					first_image_came_from_dir = False
					self.curr_img_in_list = len(inputlist)-1
		self.image_list = []
		for item in inputlist:
			if not self.closing_app:
				if os.path.isfile(item):
					if self.valid_image(item):
						if not second_image_found and first_image_found:
							second_image_found = True
							second_image = item
							second_image_came_from_dir = False
						if not first_image_found:
							first_image_found = True
							first_image = item
							first_image_came_from_dir = False
						self.image_list.append(item)
						if self.verbose:
							self.images_found += 1
							print _("Found: %(item)s [%(number)i]") % {'item': item, 'number': self.images_found}
				else:
					# If it's a directory that was explicitly selected or passed to
					# the program, get all the files in the dir.
					# Retrieve only images in the top directory specified by the user
					# unless explicitly told to recurse (via -R or in Settings>Preferences)
					folderlist.append(item)
					if not second_image_found:
						# See if we can find an image in this directory:
						self.stop_now = False
						self.expand_directory(item, True, go_buttons_enabled, False, False)
						itemnum = 0
						while itemnum < len(self.image_list) and not second_image_found:
							if os.path.isfile(self.image_list[itemnum]):
								if not second_image_found and first_image_found:
									second_image_found = True
									second_image_came_from_dir = True
									second_image = self.image_list[itemnum]
									self.set_go_navigation_sensitivities(True)
									go_buttons_enabled = True
									while gtk.events_pending():
										gtk.main_iteration(True)
								if not first_image_found:
									first_image_found = True
									first_image = self.image_list[itemnum]
									first_image_came_from_dir = True
							itemnum += 1
				# Load first image and display:
				if first_image_found and not first_image_loaded and self.curr_img_in_list <= len(self.image_list)-1:
					first_image_loaded = True
					if self.slideshow_mode:
						self.toggle_slideshow(None)
					if self.verbose and self.currimg_name != "":
						print _("Loading: %s") % self.currimg_name
					try:
						self.load_new_image2(False, False, True, True)
						# Calling load_new_image2 will reset the following two vars
						# to 0, so ensure they are -1 again (no images preloaded)
						self.preloadimg_prev_in_list = -1
						self.preloadimg_next_in_list = -1
						if not self.currimg_is_animation:
							self.previmg_width = self.currimg_pixbuf.get_width()
						else:
							self.previmg_width = self.currimg_pixbuf.get_static_image().get_width()
						self.image_loaded = True
						first_image_loaded_successfully = True
						if not self.closing_app:
							while gtk.events_pending():
								gtk.main_iteration(True)
					except:
						pass
					if first_image_came_from_dir:
						self.image_list = []
				# Pre-load second image:
				if second_image_found and not second_image_preloaded and ((not second_image_came_from_dir and self.curr_img_in_list+1 <= len(self.image_list)-1) or second_image_came_from_dir):
					second_image_preloaded = True
					temp = self.image_list
					self.image_list = []
					while len(self.image_list) < self.curr_img_in_list+1:
						self.image_list.append(first_image)
					self.image_list.append(second_image)
					self.preload_next_image(False)
					self.image_list = temp
		if first_image_found:
			# Sort the filelist and folderlist alphabetically, and recurse into folderlist:
			if first_image_came_from_dir:
				self.add_folderlist_images(folderlist, go_buttons_enabled)
				self.do_image_list_stuff(first_image, second_image)
			else:
				self.do_image_list_stuff(first_image, second_image)
				self.add_folderlist_images(folderlist, go_buttons_enabled)
			self.update_title()
			if not self.closing_app:
				while gtk.events_pending():
					gtk.main_iteration(True)
		if not first_image_loaded_successfully:
			self.image_load_failed(False, init_image)
		self.searching_for_images = False
		self.update_statusbar()
		self.set_go_navigation_sensitivities(False)
		self.set_slideshow_sensitivities()
		self.thumbpane_update_images(True, self.curr_img_in_list)
		if not self.closing_app:
			self.change_cursor(None)
		self.recursive = False

	def add_folderlist_images(self, folderlist, go_buttons_enabled):
		if len(folderlist) > 0:
			folderlist.sort(locale.strcoll)
			folderlist = list(set(folderlist))
			for item in folderlist:
				if not self.closing_app:
					if (not self.open_hidden_files and os.path.basename(item)[0] != '.') or self.open_hidden_files:
						self.stop_now = False
						self.expand_directory(item, False, go_buttons_enabled, True, True)

	def do_image_list_stuff(self, first_image, second_image):
		if len(self.image_list) > 0:
			self.set_go_navigation_sensitivities(True)
			self.image_list = list(set(self.image_list))
			self.image_list.sort(locale.strcoll)

	def expand_directory(self, item, stop_when_second_image_found, go_buttons_enabled, update_window_title, print_found_msg):
		if not self.stop_now and not self.closing_app:
			folderlist = []
			filelist = []
			if not os.access(item, os.R_OK):
				return False
			for item2 in os.listdir(item):
				if not self.closing_app and not self.stop_now:
					while gtk.events_pending():
						gtk.main_iteration(True)
					item2 = item + os.sep + item2
					item_fullpath2 = os.path.abspath(item2)
					if (not self.open_hidden_files and os.path.basename(item_fullpath2)[0] != '.') or self.open_hidden_files:
						if os.path.isfile(item_fullpath2) and self.valid_image(item_fullpath2):
							filelist.append(item2)
							if self.verbose and print_found_msg:
								self.images_found += 1
								print _("Found: %(fullpath)s [%(number)i]") % {'fullpath': item_fullpath2, 'number': self.images_found}
						elif os.path.isdir(item_fullpath2) and self.recursive:
							folderlist.append(item_fullpath2)
					elif self.verbose:
						print _("Skipping: %s") % item_fullpath2
			if len(self.image_list)>0 and update_window_title:
				self.update_title()
			# Sort the filelist and folderlist alphabetically:
			if len(filelist) > 0:
				filelist.sort(locale.strcoll)
				for item2 in filelist:
					if not item2 in self.image_list:
						self.image_list.append(item2)
						if stop_when_second_image_found and len(self.image_list)==2:
							return
						if not go_buttons_enabled and len(self.image_list) > 1:
							self.set_go_navigation_sensitivities(True)
							go_buttons_enabled = True
			# Recurse into the folderlist:
			if len(folderlist) > 0:
				folderlist.sort(locale.strcoll)
				for item2 in folderlist:
					if not self.stop_now:
						self.expand_directory(item2, stop_when_second_image_found, go_buttons_enabled, update_window_title, print_found_msg)

	def register_file_with_recent_docs(self, imgfile):
		self.recent_file_add_and_refresh(imgfile)
		if os.path.isfile(imgfile) and gtk.check_version(2, 10, 0) == None:
			try:
				gtk_recent_manager = gtk.recent_manager_get_default()
				uri = ''
				if imgfile[:7] != 'file://':
					uri = 'file://'
				uri = uri + urllib.pathname2url(os.path.abspath(imgfile))
				gtk_recent_manager.add_item(uri)
			except:
				#Isnt currently functional on win32
				if sys.platform == "win32":
					pass
				else:
					raise

	def valid_image(self, file):
		test = gtk.gdk.pixbuf_get_file_info(file)
		if test == None:
			return False
		elif test[0]['name'] == "wbmp":
			# some regular files are thought to be wbmp for whatever reason,
			# so let's check further.. :(
			try:
				test2 = gtk.gdk.pixbuf_new_from_file(file)
				return True
			except:
				return False
		else:
			return True

	def image_flip(self, old_pix, vertical):
		width = old_pix.get_width()
		height = old_pix.get_height()
		d = None
		if vertical:
			d, w, h, rws = imgfuncs.vert(old_pix.get_pixels(), width, height, old_pix.get_rowstride(), old_pix.get_n_channels())
		else:
			d, w, h, rws = imgfuncs.horiz(old_pix.get_pixels(), width, height, old_pix.get_rowstride(), old_pix.get_n_channels())
		if d:
			new_pix = gtk.gdk.pixbuf_new_from_data(d, old_pix.get_colorspace(), old_pix.get_has_alpha(), old_pix.get_bits_per_sample(), w, h, rws)
			return new_pix
		return old_pix

	def image_rotate(self, old_pix, full_angle):
		width = old_pix.get_width()
		height = old_pix.get_height()
		angle = full_angle - (int(full_angle) / 360) * 360
		if angle:
			d = None
			if angle % 270 == 0:
				d, w, h, rws = imgfuncs.right(old_pix.get_pixels(), width, height, old_pix.get_rowstride(), old_pix.get_n_channels())
			elif angle % 180 == 0:
				d, w, h, rws = imgfuncs.mirror(old_pix.get_pixels(), width, height, old_pix.get_rowstride(), old_pix.get_n_channels())
			elif angle % 90 == 0:
				d, w, h, rws = imgfuncs.left(old_pix.get_pixels(), width, height, old_pix.get_rowstride(), old_pix.get_n_channels())
			if d:
				new_pix = gtk.gdk.pixbuf_new_from_data(d, old_pix.get_colorspace(), old_pix.get_has_alpha(), old_pix.get_bits_per_sample(), w, h, rws)
				return new_pix
		return old_pix

	def toggle_slideshow(self, action):
		if len(self.image_list) > 1:
			if not self.slideshow_mode:
				if self.slideshow_in_fullscreen and not self.fullscreen_mode:
					self.enter_fullscreen(None)
				self.slideshow_mode = True
				self.update_title()
				self.set_slideshow_sensitivities()
				if not self.curr_slideshow_random:
					self.timer_delay = gobject.timeout_add(int(self.curr_slideshow_delay*1000), self.goto_next_image, "ss")
				else:
					self.reinitialize_randomlist()
					self.timer_delay = gobject.timeout_add(int(self.curr_slideshow_delay*1000), self.goto_random_image, "ss")
				self.ss_start.hide()
				self.ss_stop.show()
				timer_screensaver = gobject.timeout_add(1000, self.disable_screensaver_in_slideshow_mode)
			else:
				self.slideshow_mode = False
				gobject.source_remove(self.timer_delay)
				self.update_title()
				self.set_slideshow_sensitivities()
				self.set_zoom_sensitivities()
				self.ss_stop.hide()
				self.ss_start.show()

	def update_title(self):
		if len(self.image_list) == 0:
			title = "Mirage"
		else:
			title = "Mirage - " +_("[%(current)i of %(total)i]") % {'current': self.curr_img_in_list+1, 'total': len(self.image_list)} + ' ' + os.path.basename(self.currimg_name)
			if self.slideshow_mode:
				title = title + ' - ' + _('Slideshow Mode')
		self.window.set_title(title)

	def slideshow_controls_show(self):
		if not self.slideshow_controls_visible and not self.controls_moving:
			self.slideshow_controls_visible = True

			self.ss_delayspin.set_value(self.curr_slideshow_delay)
			self.ss_randomize.set_active(self.curr_slideshow_random)

			if self.slideshow_mode:
				self.ss_start.set_no_show_all(True)
				self.ss_stop.set_no_show_all(False)
			else:
				self.ss_start.set_no_show_all(False)
				self.ss_stop.set_no_show_all(True)

			(xpos, ypos) = self.window.get_position()
			screen = self.window.get_screen()
			self.slideshow_window.set_screen(screen)
			self.slideshow_window2.set_screen(screen)

			self.slideshow_window.show_all()
			self.slideshow_window2.show_all()
			if not self.closing_app:
				while gtk.events_pending():
					gtk.main_iteration()

			ss_winheight = self.slideshow_window.allocation.height
			ss_win2width = self.slideshow_window2.allocation.width
			winheight = self.window.allocation.height
			winwidth = self.window.allocation.width
			y = -3.0
			self.controls_moving = True
			while y < ss_winheight:
				self.slideshow_window.move(2+xpos, int(winheight-y-2))
				self.slideshow_window2.move(winwidth-ss_win2width-2+xpos, int(winheight-y-2))
				y += 0.05
				if not self.closing_app:
					while gtk.events_pending():
						gtk.main_iteration()
			self.controls_moving = False

	def slideshow_controls_hide(self):
		if self.slideshow_controls_visible and not self.controls_moving:
			self.slideshow_controls_visible = False

			(xpos, ypos) = self.window.get_position()

			ss_winheight = self.slideshow_window.allocation.height
			ss_win2width = self.slideshow_window2.allocation.width
			winheight = self.window.allocation.height
			winwidth = self.window.allocation.width
			y = float(self.slideshow_window.allocation.height*1.0)
			self.controls_moving = True
			while y > -3:
				self.slideshow_window.move(2+xpos, int(winheight-y-2))
				self.slideshow_window2.move(winwidth-ss_win2width-2+xpos, int(winheight-y-2))
				y -= 0.05
				if not self.closing_app:
					while gtk.events_pending():
						gtk.main_iteration()
			self.controls_moving = False

	def disable_screensaver_in_slideshow_mode(self):
		if self.slideshow_mode and self.disable_screensaver:
			test = os.spawnlp(os.P_WAIT, "/usr/bin/xscreensaver-command", "xscreensaver-command", "-deactivate")
			if test <> 127:
				timer_screensaver = gobject.timeout_add(1000, self.disable_screensaver_in_slideshow_mode)

	def main(self):
		gtk.main()

if __name__ == "__main__":
	base = Base()
	gtk.gdk.threads_enter()
	base.main()
	gtk.gdk.threads_leave()
