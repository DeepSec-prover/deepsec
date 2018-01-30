#!/usr/bin/python
# -*- coding: iso-8859-1 -*-
import os
import sys
import glob                     # for regexp
from time import clock, time
import subprocess
from datetime import datetime
import shlex
import argparse
import resource

import data
import utils

DEFAULT_CORES = 10
local = False                    # set to True requires configuration of DeepSeec and Porridge roots below
git_hash = str(subprocess.Popen(["git", "rev-parse", "HEAD"], stdout = subprocess.PIPE).communicate()[0])


def sortSize(listEx):
   listAssoc = [(int(ex.split(".dps")[0].split("_")[-1]), ex) for ex in listEx]
   listSorted = sorted(listAssoc, cmp=lambda (x1,x2),(y1,y2): cmp(x1, y1))
   return([ex for (nb, ex) in listSorted])

def defLimit():
   # Set maximum CPU time to 1 second in child process, after fork() but before exec()
   print "Setting resource limit in child (pid %d)" % os.getpid()
   maxRealTime = 2*3600              # 2 hours
   cpu_limit = maxRealTime
   # cpu_limit = maxRealTime
   # Limit of Memory usage (in bytes)
   mem_limit = 10*1024*1024*1024          # 10 GO ??
   soft_CPU, hard_CPU = resource.getrlimit(resource.RLIMIT_CPU)
   soft_AS, hard_AS = resource.getrlimit(resource.RLIMIT_AS)   
   resource.setrlimit(resource.RLIMIT_CPU, (cpu_limit,hard_CPU))
   resource.setrlimit(resource.RLIMIT_AS, (mem_limit,hard_AS))
   # print "CPU limit of child (pid %d)" % os.getpid(), resource.getrlimit(resource.RLIMIT_CPU)
   # print "MEMORY limit of child (pid %d)" % os.getpid(), resource.getrlimit(resource.RLIMIT_AS)
   
def main():
    # PARSING ARGSSS
    parser = argparse.ArgumentParser(description='Launch some benchmarks om DeepSec.')
    parser.add_argument('-f', '--file_log',
                        help='you can choose a name of the log file')
    parser.add_argument('-logs', '--folder_logs',
                        help='you can choose the location where log files will be put')
    parser.add_argument('-v', '--version', nargs='*',
                        help='you can choose the version of POR (none, old POR, new POR) [none,old,new]')
    parser.add_argument('-ft', '--filter_tests',
                        help='you can filter tests by giving a substrings')
    parser.add_argument('-d', '--distributed', nargs='*',
                        help='distribute the computation among given numbers of workers (default=10), choose 0 for no distribution')

    args = parser.parse_args()

    nameFile = "BENCH_results"
    if args.file_log:
        nameFile = args.file_log
    else:
       if args.version:
          nameFile = nameFile + "_" + "-".join(args.version)
       if args.filter_tests:
          nameFile = nameFile + "_" + args.filter_tests
       nameFile = nameFile + "_" + git_hash[0:5]
   
    path_logs = "log/"
    if args.folder_logs:
        path_logs = args.folder_logs
    log_all = open(path_logs + nameFile + ".log", "a")
    def print_all(s):
#        print s
        log_all.write(s)
        log_all.flush()
    def pprint_all(s):
        print s
        log_all.write(s)
        log_all.flush()
    def new(s):
        return(not("OLD/" in s))

    list_tests = glob.glob('../*/*.dps')
    list_tests = filter(lambda s : new(s), list_tests)
    timing = "/usr/bin/time -f 'Time %E / Memory %Mk' "
    bina_default = timing + '../../../deepsec  -deepsec_dir ../../../ '
    singleCore = False
    if not(args.distributed):
       bina_default += "-distributed " + str(DEFAULT_CORES) + " "
    elif int(args.distributed[0]) <= 0:
       singleCore = True
       pass
    else:
       bina_default += "-distributed " + str(args.distributed[0]) + " " 
    if not(args.version):
        args.version = ["old","new","none"]
    if args.version or args.difficulty:
        if args.version:
            print(args.version)
            list_binaries = []
            if "old" in args.version:
                list_binaries.append([bina_default, "old"])
            if "new" in args.version:
                bina = bina_default + "-with_por_gen "
                list_binaries.append([bina, "new"])
            if "none" in args.version:
                list_binaries.append([bina_default + "-no_por ", "none"])

    if args.filter_tests:
       list_tests = filter(lambda s: args.filter_tests in s, list_tests)

       # # We consider versions of tests where agents are different in each session only if we add '_diff ' to the filter.
       # if "_diff" in args.filter_tests:
       #    pattern = args.filter_tests.split("_diff")[0]
       #    list_tests = filter(lambda s: pattern in s and "diff" in s, list_tests)
       # else:
       # if args.filter_tests == "Simple":
       # if args.filter_tests == "WMF" or args.filter_tests == "WMF_diff":
       #    list_tests = sortWMF(list_tests)
       # if args.filter_tests == "AKA":
       #    list_tests = sortAKA(list_tests)

    list_tests = sortSize(list_tests)
    pprint_all("="*15 + " STARTING A NEW BENCHMARK " + "="*15 +"\n")
    pprint_all("Date: " + str(datetime.now()))
    pprint_all("Git Hash: " + git_hash)
    pprint_all("Location of log File: " + path_logs + nameFile + ".log" + "\n")

    if local:
       pass
       # TODO
       # pprint_all("DeepSec GIT: " + deepsec_git + ", Porridge GIT: " + porridge_git + "\n")    
    if not(args.version):
        print("You have used no option, are you sure? Look at the helping message above.")
    pprint_all("You chose those versions: " + str(args.version) + "\n" +
               "On all those examples: " + str(list_tests) + "\n")
    raw_input("Press Enter to launch all benchmarks...")

   # BENCHMARKS
    HEAD = " " + "#"*10 + " "
    HEADA = " " + "-"*3 + " "
    IND = " " * 50

    # defLimit()                  # limit of CPU and memory usage
    for b in list_binaries:
        binary = b[0]
        b_name = b[1]
        pprint_all("\n" + HEAD + "Starting a benchmark version: " + b_name + HEAD)
        log_all.write("\n")
        pprint_all(IND + str(datetime.now()) + "\n")
        for file in list_tests:
            killed = True
            t_name = file.split("/")[-1].split(".dps")[0]
            pprint_all(HEADA + "Benchmark of Protocol: " + t_name + HEADA)
            log_all.write("\n")
            pprint_all(IND + str(datetime.now()) + "\n") # timestamp
            log_t_b = open(path_logs + "byFiles/" + t_name + "_" + b_name + ".log", "w+")
            log_t_b.write(IND + str(datetime.now()))
            args = shlex.split(binary + " " +  file)
            memoryKilled = False
            print_all(" ".join(args) + "\n")
            print(" ".join(args))
            if singleCore:
               print_all("[NOT DISTRIBUTED]\n")               
            try:
               proc = subprocess.Popen(args,
                                       stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT,
                                       preexec_fn=defLimit())
               for line in iter(proc.stdout.readline,''):
                  line_t = line.rstrip()
                  if ("Time " in line_t or "Query" in line_t) or ("Running" in line_t) or ("s." in line_t) or ("[G-POR]" in line_t and "traces" in line_t) or "Stats" in line_t or "Out of memory" in line_t or "exception" in line_t or "Stack overflow" in line_t:
                     if "Query" in line_t:
                        killed = False
                     print_all(line_t + "\n")
                     print(line_t)
                  else:
                     # print(line_t)
                     pass
                  log_t_b.write(line_t + "\n")
                  log_t_b.flush()
            except MemoryError:
               # Stuff to reduce size of vocabulary
               memoryKilled = True
            if killed or memoryKilled:
               if memoryKilled:
                  print_all("[[KILLED]] [MEMORY] because of memory consumption >10GO." + "\n")
                  print("[[KILLED]] [MEMORY] because of memory consumption >10GO.")
               else:
                  print_all("[[KILLED]] because of timeout or memory consumption >10GO." + "\n")
                  print("[[KILLED]] because of timeout or memory consumption >10GO.")
            log_t_b.write("\n")
            pprint_all("\n")
        log_t_b.write("\n")
        pprint_all("\n")

main()