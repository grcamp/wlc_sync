#!/usr/bin/env python
#########################################################################
# Gregory Camp
# grcamp@cisco.com
# wlc_upgrade.py has multiple functions required to upgrade legacy
#    wireless LAN controllers to the correct destination codes.
#
# Testing Summary:
#    Primarily tested with NM-AIR-WLC8-K9 modules running 4.2.207.0, but
#    all WLCs should work.  Used python 2.7 with cygwin running the built-in
#    paramiko module.
#    
# Supported Methods:
#    1.  Discover AP and WLC info
#    2.  Download Software
#    3.    Run pre-upgrade checks and upgrade
#    4.  Run post 7.0.252.0 upgrade configs (enable lifetime-check bypass and set clock)
#    5.  Run post checks
#
# Planned Future Work:
#    1.  Support TFTP download Method
#    2.  Support completed automated deployment with command line arguments
#    3.  Documentation (This needs a lot of commenting)
#
# Global Variables:
#    logFile = postfix for dumping commands and raw output from WLCs
#    currentDevice = for tracking multithreading method execution
#    deviceCount = for tracking multithreading method execution
#
# User Input
#    Different Per Method
#########################################################################

# Import a whole bunch of classes, all shoul
import sys, os, getpass, paramiko, time, datetime, socket, itertools, operator, random, argparse, logging
from multiprocessing.dummy import Pool as ThreadPool
from functools import partial

# Declare global variables
logger = logging.getLogger(__name__)
WORKER_COUNT = 25
deviceCount = 0


def warning(msg):
    logger.warning(msg)


def error(msg):
    logger.error(msg)


def fatal(msg):
    logger.fatal(msg)
    exit(1)


# Global Constants and Variables
logFilePostfix = "_wlc_upgrade.log"
currentDevice = 0
deviceCount = 0


#########################################################################
# Class CiscoAP
#
# Container for all service now data attributes and functions to discover
#    and parse SSH session data
#########################################################################
class CiscoAP:
    def __init__(self, name, wlc, mac, model, softwareVersion="", serialNumber=""):
        # Declare variables
        self.name = name
        self.wlc = wlc
        self.mac = mac
        self.model = model
        self.softwareVersion = softwareVersion
        self.serialNumber = serialNumber
        self.certExpirationDate = ""
        self.certExpirationEpoch = 0
        self.aRadioStatus = ""
        self.bRadioStatus = ""


#########################################################################
# Class CiscoWLC
#
# Container for all service now data attributes and functions to discover
#    and parse SSH session data
#########################################################################
class CiscoWLC:
    # Method __init__ initializes the class variables
    #
    # Input: None
    # Output: None
    # Parameters: string ipAddress
    #
    # Return Value: None
    #####################################################################
    def __init__(self, ipAddress, username, password):
        self.ipAddress = ipAddress
        self.username = username
        self.password = password
        self.name = ""
        self.model = ""
        self.softwareVersion = ""
        self.fus = ""
        self.primaryBoot = ""
        self.backupBoot = ""
        self.activeBoot = ""
        self.serialNumber = ""
        self.apNumber = ""
        self.wlanNumber = ""
        self.authenticatedClients = ""
        self.firstApCertExpirationDate = ""
        self.runConfigCommands = ""
        self.flexconnectGroups = []

    def _wait_for_prompt(self, remote_conn, myLogFile, prompt=">", timeout=10):
        '''

        :param remote_conn:
        :param myLogFile:
        :param prompt:
        :param timeout:
        :return:
        '''
        # Declare variables
        myOutput = ""
        allOutput = ""
        i = 0

        # Change blocking mode to non-blocking
        remote_conn.setblocking(0)

        # Wait timeout seconds total
        while i < timeout:
            time.sleep(1)

            try:
                myOutput = remote_conn.recv(65535)
            except:
                myOutput = ""

            allOutput = allOutput + myOutput

            myLogFile.write(myOutput)
            myLogFile.flush()

            if prompt in myOutput:
                i = timeout

            i = i + 1

        # Change blocking mode to blocking
        remote_conn.setblocking(1)

        # Return None
        return allOutput

    def discover_device(self):
        '''
        :return:
        '''
        # Check if IP address string is empty
        if self.ipAddress == "":
            # Return error
            return -1

        # Open Log File
        myLogFile = open(self.ipAddress + logFilePostfix, 'a')
        # Attempt to login to devices via SSH
        try:
            # Attempt Login
            remote_conn_pre = paramiko.SSHClient()
            # Bypass SSH Key accept policy
            remote_conn_pre.set_missing_host_key_policy(paramiko.AutoAddPolicy())
            # Attempt to connection
            remote_conn_pre.connect(self.ipAddress, username=self.username, password=self.password, look_for_keys=False,
                                    allow_agent=False)
            # Log into WLC
            remote_conn = remote_conn_pre.invoke_shell()
            time.sleep(15)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)

            # Check if user prompt appears
            if "User:" not in myOutput:
                myLogFile.close()
                remote_conn.close()
                return -1

            remote_conn.send(self.username)
            remote_conn.send("\n")
            time.sleep(1)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()
            remote_conn.send(self.password)
            remote_conn.send("\n")
            time.sleep(15)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()

            # Check if user prompt appears
            if ">" not in myOutput:
                myLogFile.close()
                remote_conn.close()
                return -2

            # Disable paging
            remote_conn.send("config paging disable")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)

            # Find System Name, FUS, Software Version
            remote_conn.send("show sysinfo")
            remote_conn.send("\n")
            time.sleep(1)
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            self.name = split_string(myOutput.split("\n"), 'System Name', ' ', 2)
            self.fus = split_string(myOutput.split("\n"), 'Field Recovery Image Version', ' ', 4)
            self.softwareVersion = split_string(myOutput.split("\n"), 'Product Version', ' ', 2)
            self.wlanNumber = split_string(myOutput.split("\n"), 'Number of WLANs', ' ', 3)
            # Find number of authenticated clients
            self._find_authenticated_client_count(remote_conn, myLogFile)
            # Find PID and Serial Number
            remote_conn.send("show inventory")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            self.model = split_string(myOutput.split("\n"), 'PID:', ' ', 1)
            self.model = self.model.replace(',', '')
            self.serialNumber = split_string(myOutput.split("\n"), 'PID:', ' ', 7)
            # Check certificate bypass config
            self._check_certificate_bypass(remote_conn, myLogFile)
            # Find Primary and Backup Boot Images
            remote_conn.send("show boot")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            self.primaryBoot = split_string(myOutput.split("\n"), 'Primary Boot Image', ' ', 3)
            self.backupBoot = split_string(myOutput.split("\n"), 'Backup Boot Image', ' ', 3)
            self.activeBoot = split_string(myOutput.split("\n"), 'active', ' ', 0)
            # Build AP List
            remote_conn.send("show ap summary")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            self.apNumber = split_string(myOutput.split("\n"), 'Number of APs', ' ', 3)
            # self._build_ap_list(myOutput, remote_conn, myLogFile)
            # Gather run-config commands
            remote_conn.send("show run-config commands")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            self.runConfigCommands = myOutput
            # Build list of flex-connect APs
            self._build_flexconnect_group_list()
            # Enable config paging
            remote_conn.send("config paging enable")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            # Logout        
            remote_conn.send("logout")
            remote_conn.send("\n")
            time.sleep(1)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()

            # If asked to save config select No
            if "(y/N)" in myOutput:
                remote_conn.send("N")
                remote_conn.send("\n")
                time.sleep(1)

            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()
            # Close connection
            remote_conn.close()
            myLogFile.close()
        # Print exception and return -1
        except IOError as error:
            print("Invalid Hostname")
            myLogFile.close()
            return -1
        except paramiko.PasswordRequiredException as error:
            print("Invalid Username or password")
            myLogFile.close()
            return -2
        except paramiko.AuthenticationException as error:
            print("Invalid Username or password")
            myLogFile.close()
            return -2
        except socket.timeout as error:
            print("Connection timeout")
            myLogFile.close()
            return -1
        except Exception, e:
            print(str(e))
            myLogFile.close()
            return -1

        # Return success
        return 0

    # Method _check_certificate_bypass
    #
    # Input: None
    # Output: None
    # Parameters: None
    #
    # Return Value: None
    #####################################################################
    def _check_certificate_bypass(self, remote_conn, myLogFile):
        # Gather client summary
        remote_conn.send("show certificate summary")
        remote_conn.send("\n")
        myOutput = self._wait_for_prompt(remote_conn, myLogFile)
        # Parse output for each AP
        lines = myOutput.split("\n")

        # Check line for MIC and SSC lifetime check disabled
        for line in lines:
            if ("Lifetime Check for MIC" in line) and ("Enable" in line):
                self.micBypassEnabled = True
            elif ("Lifetime Check for SSC" in line) and ("Enable" in line):
                self.sscBypassEnabled = True

        # Return None
        return None

    # Method _find_authenticated_client_count
    #
    # Input: None
    # Output: None
    # Parameters: None
    #
    # Return Value: None
    #####################################################################
    def _find_authenticated_client_count(self, remote_conn, myLogFile):
        # Declare variables
        authClientCount = 0

        # Gather client summary
        remote_conn.send("show client summary")
        remote_conn.send("\n")
        myOutput = self._wait_for_prompt(remote_conn, myLogFile)
        # Parse output for each AP
        lines = myOutput.split("\n")

        # Search output for APs and build list
        for line in lines:
            if ("Associated" in line) and ("Yes" in line):
                authClientCount = authClientCount + 1

        # Set authenticated client count
        self.authenticatedClients = str(authClientCount)

        # Return None
        return None

    # Method _build_ap_list
    #
    # Input: None
    # Output: None
    # Parameters: None
    #
    # Return Value: None
    #####################################################################
    def _build_ap_list(self, output, remote_conn, myLogFile):
        # Parse output for each AP
        lines = output.split("\n")
        # Clear Current AP List
        self.apList = []

        # Search output for APs and build list
        for line in lines:
            if "-K9" in line:
                myAP = CiscoAP(line.split()[0], self.name, line.split()[3], line.split()[2], self.softwareVersion)
                self.apList.append(myAP)

        # For each ap in the list find the serial number and software version
        for ap in self.apList:
            remote_conn.send("show ap inventory " + ap.name)
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)
            ap.serialNumber = split_string(myOutput.split("\n"), 'PID: AIR-', ':', 3)
            ap.serialNumber = ap.serialNumber.strip()
            ap.calculateExpirationDate()

            # Find 802.11a Radio Status
            remote_conn.send("show ap config 802.11a " + ap.name)
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)

            if "Operation State ............................. UP" in myOutput:
                ap.aRadioStatus = "UP"
            else:
                ap.aRadioStatus = "DOWN"

            # Find 802.11b Radio Status
            remote_conn.send("show ap config 802.11b " + ap.name)
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)

            if "Operation State ............................. UP" in myOutput:
                ap.bRadioStatus = "UP"
            else:
                ap.bRadioStatus = "DOWN"

        # Sort the list and find the first ap certificate expiration date, then sort by name
        if len(self.apList) > 0:
            # Copy list and find first cert expiration
            self.apList.sort(key=operator.attrgetter('certExpirationEpoch'))
            self.firstApCertExpirationDate = self.apList[0].certExpirationDate

            # Sort ap list by name
            self.apList.sort(key=operator.attrgetter('name'))

        # Return Nothing
        return None

    def _build_flexconnect_group_list(self):
        '''

        :return:
        '''
        # Declare variables
        lines = self.runConfigCommands.split('\n')

        # Check each line for flex-connect config
        for line in lines:
            if line.strip().startswith("flexconnect group") and line.strip().endswith("add"):
                self.flexconnectGroups.append({'name': line.strip().split()[2],
                                               'ap_macs': []})
            elif line.strip().startswith("flexconnect group") and " ap add " in line.strip():
                for group in self.flexconnectGroups:
                    if line.strip().split()[2] == group['name']:
                        group['ap_macs'].append(line.strip().split()[5])

        # Return None
        return None

    def run_commands(self, commmands, saveConfig=False):
        '''

        :param commmands:
        :return:
        '''
        # Check if IP address string is empty
        if self.ipAddress == "":
            # Return error
            return -1

        # Open Log File
        myLogFile = open(self.ipAddress + logFilePostfix, 'a')
        # Attempt to login to devices via SSH
        try:
            # Attempt Login
            remote_conn_pre = paramiko.SSHClient()
            # Bypass SSH Key accept policy
            remote_conn_pre.set_missing_host_key_policy(paramiko.AutoAddPolicy())
            # Attempt to connection
            remote_conn_pre.connect(self.ipAddress, username=self.username, password=self.password, look_for_keys=False,
                                    allow_agent=False)
            # Log into WLC
            remote_conn = remote_conn_pre.invoke_shell()
            time.sleep(15)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)

            # Check if user prompt appears
            if "User:" not in myOutput:
                myLogFile.close()
                remote_conn.close()
                return -1

            remote_conn.send(self.username)
            remote_conn.send("\n")
            time.sleep(1)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()
            remote_conn.send(self.password)
            remote_conn.send("\n")
            time.sleep(15)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()

            # Check if user prompt appears
            if ">" not in myOutput:
                myLogFile.close()
                remote_conn.close()
                return -2

            # Disable paging
            remote_conn.send("config paging disable")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)

            # Run each command
            for command in commands:
                remote_conn.send(command)
                remote_conn.send("\n")
                myOutput = self._wait_for_prompt(remote_conn, myLogFile)

            # Enable config paging
            remote_conn.send("config paging enable")
            remote_conn.send("\n")
            myOutput = self._wait_for_prompt(remote_conn, myLogFile)

            # Check if config should be saved
            if saveConfig:
                remote_conn.send("save config")
                remote_conn.send("\n")
                myOutput = self._wait_for_prompt(remote_conn, myLogFile, ")")
                remote_conn.send("y")
                remote_conn.send("\n")
                myOutput = self._wait_for_prompt(remote_conn, myLogFile, ")")

            # Logout
            remote_conn.send("logout")
            remote_conn.send("\n")
            time.sleep(1)
            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()

            # If asked to save config select No
            if "(y/N)" in myOutput:
                remote_conn.send("y")
                remote_conn.send("\n")
                time.sleep(1)

            myOutput = remote_conn.recv(65535)
            myLogFile.write(myOutput)
            myLogFile.flush()
            # Close connection
            remote_conn.close()
            myLogFile.close()
        # Print exception and return -1
        except IOError as error:
            print("Invalid Hostname")
            myLogFile.close()
            return -1
        except paramiko.PasswordRequiredException as error:
            print("Invalid Username or password")
            myLogFile.close()
            return -2
        except paramiko.AuthenticationException as error:
            print("Invalid Username or password")
            myLogFile.close()
            return -2
        except socket.timeout as error:
            print("Connection timeout")
            myLogFile.close()
            return -1
        except Exception, e:
            print(str(e))
            myLogFile.close()
            return -1

        # Return success
        return 0

    def to_string(self):
        '''

        :return:
        '''
        # Gather WLC Info
        returnString = self.name + "," + self.ipAddress + "," + self.model + "," + self.serialNumber + "," + self.softwareVersion \
                       + "," + self.fus + "," + self.primaryBoot + "," + self.backupBoot + "," + self.activeBoot + "," + self.apNumber + "," \
                       + self.wlanNumber + "," + self.authenticatedClients + "," + self.firstApCertExpirationDate

        # Return string value
        return returnString


def index_containing_substring(the_list, substring):
    '''
    :param the_list:
    :param substring:
    :return:
    '''
    # For searches each string in the_list for an occurrence of substring
    for i, s in enumerate(the_list):
        # If substring is contained in s return current index
        if substring in s:
            return i
    # Return -1 if substring is not found in the_list
    return -1


def split_string(the_list, sub_string, delimiter, string_index):
    '''
    :param the_list:
    :param sub_string:
    :param delimiter:
    :param string_index:
    :return:
    '''
    listVal = index_containing_substring(the_list, sub_string)
    if listVal == -1:
        returnVal = 'N/A'
        return returnVal
    else:
        returnVal = the_list[listVal].split(delimiter)[string_index]
        returnVal = returnVal.strip()
    return returnVal


def find_ap_changes(sourceFlexGroups, destinationFlexGroups):
    # Create list of commands to run
    commands = []

    # Search through each source group
    for group in sourceFlexGroups:
        # Check if group exists in destination
        for dGroup in destinationFlexGroups:
            if group['name'] == dGroup['name']:
                for ap in group['ap_macs']:
                    if any(ap == s for s in dGroup['ap_macs']) == False:
                        commands.append("config flexconnect group {} ap add {}".format(group['name'], ap))

    # Search through each destination group
    for group in destinationFlexGroups:
        # Check if group exists in source
        for sGroup in sourceFlexGroups:
            if group['name'] == sGroup['name']:
                for ap in group['ap_macs']:
                    if any(ap == s for s in sGroup['ap_macs']) == False:
                        commands.append("config flexconnect group {} ap delete {}".format(group['name'], ap))

    # Return commandList
    return commands


def main(**kwargs):
    '''
    :param kwargs:
    :return:
    '''

    # Set logging
    logging.basicConfig(stream=sys.stderr, level=logging.INFO, format="%(asctime)s [%(levelname)8s]:  %(message)s")

    if kwargs:
        args = kwargs
    else:
        # Identify command line arguments
        parser = argparse.ArgumentParser()
        parser.add_argument('sourceWLCip', help='company key of an NP account (can be found in any NP URL)')
        parser.add_argument('destinationWLCip', help='company key of an NP account (can be found in any NP URL)')
        parser.add_argument('-u', '--username', help='CEC username')
        parser.add_argument('-p', '--password', help='CEC password (prompted safely on the CLI if not given)')
        parser.add_argument('--flexconnect_groups', help='Sync Flex Connect Groups')
        args = parser.parse_args()

    # Prompt for username if not set
    if not args.username:
        args.username = getpass.getuser()

    # Prompt for password if not set
    if not args.password:
        args.password = getpass.getpass()

    # Create WLC and discover device
    sourceWLC = CiscoWLC(args.sourceWLCip.strip(), args.username, args.password)
    logger.info("Starting Discovery for WLC {}".format(sourceWLC.ipAddress))
    sourceWLC.discover_device()
    logger.info("Completed Discovery for WLC {}".format(sourceWLC.ipAddress))

    # Create WLC and discover device
    destinationWLC = CiscoWLC(args.destinationWLCip.strip(), args.username, args.password)
    logger.info("Starting Discovery for WLC {}".format(destinationWLC.ipAddress))
    destinationWLC.discover_device()
    logger.info("Completed Discovery for WLC {}".format(destinationWLC.ipAddress))

    # Build command list
    logger.info("Building Command List for Sync")
    commands = find_ap_changes(sourceWLC.flexconnectGroups, destinationWLC.flexconnectGroups)
    logger.info("Completed Command List for Sync")


    for command in commands:
        print(command)

    # Sync Config
    logger.info("Starting WLC Config Push to {}".format(destinationWLC.ipAddress))
    destinationWLC.run_commands(commands)
    logger.info("Completed WLC Config Push to {}".format(destinationWLC.ipAddress))

    # Return None
    return None


if __name__ == '__main__':
    try:
        main()
    except Exception, e:
        print str(e)
        os._exit(1)
