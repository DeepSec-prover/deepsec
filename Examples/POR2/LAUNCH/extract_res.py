#!/usr/bin/python
# -*- coding: iso-8859-1 -*-
import os
import sys
import glob                     # for regexp
from time import clock, time
import subprocess
from datetime import datetime, timedelta
import shlex
import argparse
import pprint
import logging
import math
import marshal
import argparse

import dateutil.parser
from texttable import *

import data
from utils import *

parser = argparse.ArgumentParser(description='Extract results of benchmarks from log files.')
parser.add_argument('--latex',
                    help='you can choose to write all extracted results in a Latex file')
parser.add_argument('--explo',
                    help='to display number of explorations instead of time')
parser.add_argument('--logs', nargs='*',
                    help='location of log files. Default=.')

args = parser.parse_args()
isLoad = True
dicoAppend = {}

# -- LOGGING --
rootLogger = logging.getLogger()
rootLogger.setLevel(logging.DEBUG)
DATEFMT_L = "%m-%d %H:%M:%S"
DATEFMT_S = "%d %H:%M:%S"
# logging.basicConfig(stream=sys.stdout,
#                     level=logging.WARNING,
#                     format="%(message)s")
err=logging.FileHandler("summary/LOG_err.log")
warn=logging.FileHandler("summary/LOG_warn.log")
debug=logging.FileHandler("summary/LOG_debug.log")

logFormatter = logging.Formatter("%(asctime)s [%(levelname)-5.5s] | %(message)s",
                                 datefmt=DATEFMT_L)
warn.setFormatter(logFormatter)
err.setFormatter(logFormatter)
debug.setFormatter(logFormatter)
warn.setLevel(logging.WARNING)
err.setLevel(logging.ERROR)
debug.setLevel(logging.DEBUG)

# Files
rootLogger.addHandler(warn)
rootLogger.addHandler(debug)
rootLogger.addHandler(err)

# Stdout
handler = logging.FileHandler("to_rm")
# stream=sys.stderr,
#                               format='%(asctime)s [%(levelname)-5.5s] | %(message)s",',
#                               level=logging.WARNING)
handler.setFormatter(logFormatter)
handler.setLevel(logging.WARNING)
rootLogger.addHandler(handler)

# -- OPTIONS AND DATA (from data.py) --
TESTSDICO = data.get_testsDico()
VERSDICO = data.get_versDico()

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def print2(s):
    print(s)
    logging.debug(s)


# --------------------------- MAIN ------------------------------------------ #
def main():
    nameFile = "summary"
    log_all = open("summary/" + nameFile + ".log", "a")
    def print_all(s):
        log_all.write(s)
        log_all.flush()
    def pprint_all(s):
        print s
        log_all.write(s)
        log_all.flush()

    pp = pprint.PrettyPrinter(indent=1)
    nbTests = 0
    nbVers = 0
    nbNewTests = 0
    nbRewrite = 0
    list_binaries_tout = glob.glob('../../deepsec*')
    listLog = glob.glob('log/*.log')
    path_log = 'log/'
    if args.logs:
        path_log = args.logs[0] + '/log/'
        listLog = glob.glob(path_log + '*.log')
    print("There are %d log files." % len(listLog))
    dicoPath = "summary/DumpRes.json"
    TestsDico = TESTSDICO
    if not(args.logs) and isLoad and (os.path.exists(dicoPath)):
        dicoFile = open(dicoPath, 'rb')
        VersionsDico = marshal.load(dicoFile)
        dicoFile.close()
    else:
        VersionsDico = VERSDICO
    VersionsDico = setNoNew(VersionsDico)
    for log in listLog:
        logging.debug("=" * 20 + "   NEW logFile   " + "=" * 20)
        logging.debug("logFile: " + log + "\n")
        logFile = open(log, 'r')
        logText = logFile.read()
        bench = extractBench(logText) # extract last benchmarks, with associated text
        listVers = extractVers(bench) # extract list of versions, associated text
        # listVers: list of pairs (version, raw bench)
        for el in listVers:
            nbVers = nbVers + 1
            (version, benchVers) = el
            version = version.strip()
            versionKey = version #findVers(version, VersionsDico)
            if not(versionKey in VersionsDico):
                print("Cannot find version '%s' in data.py..." % version)
                continue
            versionDico = VersionsDico[versionKey] 
            versionName = versionDico["name"]
            logging.debug(" ----- NEW version: " + versionName + " ----- ")
            listTests = extractTests(benchVers)
            # listTests: list of pairs (test, raw bench)
            for el in listTests:
                (test, benchTests) = el
                isKilled = "KILLED" in benchTests or "Out of memory" in benchTests or "Stack overflow" in benchTests
                if not("Running time: " in benchTests) and not(isKilled):
                    logging.debug("new test: " + test)
                    logging.debug("Test is not yet finished...")
                else:
                    nbTests = nbTests + 1
                    testName = test.split(".")[0]
                    testFile = test.strip() + ".txt"
                    isTrue = ("Equivalent " in benchTests or isKilled)
                    date = benchTests.splitlines()[1].strip()
                    testKey = findTest(testFile, TestsDico)
                    if testKey == "" or testKey == None:
                        logging.critical("The tests %s cannot be found.\n" % testFile)
                        # continue
                        #   testKey = testFile.split("-")[0] + "_" + testFile.split("-")[1] + "_" + testFile.split("-")[-1].split(".txt")[0]
                        number = testFile.split("_")[-1].split(".")[0]
                        testName = testFile.split(".")[0]
                        testKey = testName
                        testDico = {
                            'res' : isTrue,
                            'name' : " ",
                            'file' : testFile,
                            'cat' : 12
                        }
                        dicoAppend[testKey] = testDico
                    else:
                        testDico = TestsDico[testKey]
                    if not(isKilled) and (testDico['res'] != isTrue):
                        print("NOT EXPECTED RESULT. The version %s on test %s answerd %s."
                              % (versionName, testName, str(isTrue)))
                    if "Number of explorations" in benchTests:
                        explo = benchTests.split("Number of explorations")[1]
                        nbExplo = int(explo.split("[")[1].split("]")[0])
                        nbStop = int(explo.split("[")[2].split("]")[0])                        
                    else:
                        nbExplo = -1
                        nbStop = -1
                    if "KILLED" in benchTests or "Out of memory" in benchTests:
                        killed = True
                    else:
                        timeString = benchTests.split("Time ")[1].split("/")[0].strip()
                        killed = False
                    logging.debug("New test: " + testName + "|: True? " + str(isTrue) + ", nbExplo: " + str(nbExplo) +
                                  ", nbStop: " + str(nbStop) + ", killed?: " + str(killed) + 
                                 ", date: " + date + ", time: " + str(timeString) + "  |  ")
                    parse = timeString
                    if not "." in parse:
                        time = (float(parse.split(":")[0])*60*60 +
                                float(parse.split(":")[1])*60 +
                                float(parse.split(":")[2]))
                    else:
                        time = (float(parse.split(":")[0])*60 +
                                float(parse.split(":")[1].split(".")[0]) +
                                float(parse.split(":")[1].split(".")[1])/100)
                    logAll = open(path_log + "byFiles/" + testFile.split(".")[0] + "_" +version + ".log"  , 'r').read()
                    if killed:
                        if "[MEMORY]" in benchTests or "Out of memory" in logAll or "Stack overflow" in logAll:
                            killed = "MemOut"
                        else:
                            killed = "TimeOut"
                    else:
                        killed = ""
                    testDico = {
                        "new" : True,        # bool
                        "file": testFile,    # str
                        "res" : killed or isTrue, # bool
                        "date" : date,       # string
                        "time_string" : timeString,       # str
                        "time" : time,        # int
                        "killed" : killed,   # string
                        "nbExplo" : nbExplo, # int
                        "fileFrom": log,     # string
                    }
                    if testName in versionDico["benchs"]:
                        oldTest = versionDico["benchs"][testName]
                        oldDate = oldTest["date"]
                        oldTime = oldTest["time"]
                        oldFile = oldTest["fileFrom"]
                        diff = math.fabs(oldTime - time)
                        if max(time,oldTime) == 0:
                            diffRel = 0
                        else:
                            diffRel = (diff / max(time,oldTime))
                        overWrite = ""
                        isOverWrite = False
                        comm = ""
                        if (dateutil.parser.parse(date) > dateutil.parser.parse(oldDate)):
                            nbRewrite = nbRewrite + 1
                            overWrite = " --> OVERWRITTEN! "
                            versionDico["benchs"][testName] = testDico
                            isOverWrite = True
                        toPrint = (("Diff rel: %f%s--- %sClash for version %s on test %s.   --- Difference: %f.\n" +
                                    " " * 30 + "OLD/NEW for time: %f/%f, Date: %s / %s" +
                                    ", logFile: %s/%s.") %
                                   (diffRel, comm, overWrite, versionKey, testName, diff, oldTime, time, oldDate, date, oldFile, log))
                        if comm != "":
                            logging.info(toPrint)
                        elif diffRel > 0.2:
                            logging.critical(toPrint)
                            print(toPrint)
                        elif diffRel > 0.07:
                            logging.error(toPrint)
                        elif isOverWrite:
                            logging.warning(toPrint)
                        elif diffRel > 0.0001:
                            logging.debug(toPrint)
                    else:
                        nbNewTests = nbNewTests + 1
                        versionDico["benchs"][testName] = testDico
                        logging.critical(("----------------------------------------------- NEW RESULT:"
                                          "Version %s on test %s. Time: %f, nbExplo: %d.")
                                         % (versionName, testName, time, nbExplo))
            logging.debug("\n")


    print2("\n~~~~~~~~~ Some Stats ~~~~~~~~~\n" +
          "Nb. of Tests: %d. Number of versions: %d. Number of new tests: %d. Number of rewrites: %d." % (nbTests, nbVers, nbNewTests, nbRewrite))

    print2("\n~~~~~~~~~ Results ~~~~~~~~~")
    testsFlag = "all"

    toPrint = fromVersToTests(VersionsDico, TestsDico, vers="all", tests=testsFlag, disp=args.explo)

    logging.debug(toPrint)
    toPrintColor = toPrint
    toPrintColor = toPrintColor.replace(">(", bcolors.HEADER + "  ")
    toPrintColor = toPrintColor.replace(")", bcolors.ENDC + " ")
    toPrintColor = toPrintColor.replace(" > ", " > " + bcolors.FAIL)
    toPrintColor = toPrintColor.replace("< ", bcolors.ENDC + "< ")
    toPrintColor = toPrintColor.replace("->", "->" + bcolors.WARNING)
    toPrintColor = toPrintColor.replace("<-", bcolors.ENDC + "<-")
    toPrintColor = toPrintColor.replace(" [", " [" )
    toPrintColor = toPrintColor.replace("] ", bcolors.ENDC + "] ")
    toPrintColor = toPrintColor.replace(" . ", bcolors.OKBLUE + " . " + bcolors.ENDC)


    print(toPrintColor)
    print2("Captions: [> X <] if the returned result is false, [.] if is there is no benchmark, [-> t <-] for new tests, [TimeOut] if we killed the process because either it took more than 2 hours, [MemOut] when it consumed more than 15GO of RAM (warning: the reason of the kill may be missinterpreted), and [[t]] if test performed in the last 2 hours.")
    logging.error("#" * 80 + "\n")

    if not(args.logs):
        dicoFile = open(dicoPath, 'wb')
        marshal.dump(VersionsDico, dicoFile)
        dicoFile.close()

    
    if args.latex:
        fileLatex = open(args.latex, 'w')
        fileLatex.write(str(fromVersToTests(VersionsDico, TestsDico, toLatex=True, vers="paper", tests="notall", disp=args.explo)))
        fileLatex.close()
    print(dicoAppend)
main()
