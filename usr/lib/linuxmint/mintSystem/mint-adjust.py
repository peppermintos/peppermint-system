#!/usr/bin/python

import os
import commands
import sys
from time import strftime

# Prepare the log file
global logfile
logfile = open("/var/log/mintsystem.log", "w")


def log(string):
    logfile.writelines("%s - %s\n" % (strftime("%Y-%m-%d %H:%M:%S"), string))
    logfile.flush()

log("mintSystem started")

try:
    # Read configuration
    sys.path.append('/usr/lib/linuxmint/common')
    from configobj import ConfigObj
    config = ConfigObj("/etc/linuxmint/mintSystem.conf")

    # Default values
    if ('global' not in config):
        config['global'] = {}
    if ('enabled' not in config['global']):
        config['global']['enabled'] = "True"
    if ('restore' not in config):
        config['restore'] = {}

    config.write()

    # Exit if disabled
    if (config['global']['enabled'] == "False"):
        log("Disabled - Exited")
        sys.exit(0)

    adjustment_directory = "/etc/linuxmint/adjustments/"

    # Perform file execution adjustments
    for filename in os.listdir(adjustment_directory):
        basename, extension = os.path.splitext(filename)
        if extension == ".execute":
            full_path = adjustment_directory + "/" + filename
            os.system(full_path)
            log("%s executed" % full_path)

    # Perform file overwriting adjustments
    array_preserves = []
    if os.path.exists(adjustment_directory):
        for filename in os.listdir(adjustment_directory):
            basename, extension = os.path.splitext(filename)
            if extension == ".preserve":
                with open(adjustment_directory + "/" + filename) as filehandle:
                    for line in filehandle:
                        line = line.strip()
                        array_preserves.append(line)
    overwrites = {}
    if os.path.exists(adjustment_directory):
        for filename in sorted(os.listdir(adjustment_directory)):
            basename, extension = os.path.splitext(filename)
            if extension == ".overwrite":
                filehandle = open(adjustment_directory + "/" + filename)
                with open(adjustment_directory + "/" + filename) as filehandle:
                    for line in filehandle:
                        line = line.strip()
                        line_items = line.split()
                        if len(line_items) == 2:
                            source, destination = line.split()
                            if destination not in array_preserves:
                                overwrites[destination] = source

    for key in overwrites.keys():
        source = overwrites[key]
        destination = key
        if os.path.exists(source):
            if "*" not in destination:
                # Simple destination, do a cp
                if os.path.exists(destination):
                    os.system("cp " + source + " " + destination)
                    log(destination + " overwritten with " + source)
            else:
                # Wildcard destination, find all possible matching destinations
                matching_destinations = commands.getoutput("find " + destination)
                matching_destinations = matching_destinations.split("\n")
                for matching_destination in matching_destinations:
                    matching_destination = matching_destination.strip()
                    if os.path.exists(matching_destination):
                        os.system("cp " + source + " " + matching_destination)
                        log(matching_destination + " overwritten with " + source)

except Exception, detail:
    print detail
    log(detail)

log("mintSystem stopped")
logfile.close()
