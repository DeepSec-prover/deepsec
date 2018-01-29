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
import re

import dateutil.parser
from texttable import *
from tabulate import tabulate

import data_gen

# SETTINGS FOR PRETTY PRINTINGS
# First Column' width
firstWidth = 22
# Others Columns' width
width = 13


def extractBench(text):
    lastBench = text.split("=============== STARTING A NEW BENCHMARK ===============")[-1]
    return(lastBench)

def extractVers(text):
    SEP = "##########"
    if not(SEP in text):
        return []
    listVers = text.split(SEP)[1:]
    listVers2 = []
    i = 0
    while(i <len(listVers)):
        vers = listVers[i].split(": ")[1]
        benchVers = listVers[i+1]
        listVers2.append((vers, benchVers))
        i = i + 2
    return(listVers2)

def extractTests(text):
    SEP = "--- Benchmark"
    if not(SEP in text):
        return []
    listTests = text.split(SEP)[1:]
    listTests2 = []
    i = 0
    for test in listTests:
        header = test.split(" --- ")[0]
        body = " --- ".join(test.split(" --- ")[1:])
        vers = header.split(": ")[1]
        listTests2.append((vers, body))
    return(listTests2)

def findVers(call, dicoVersions):
    res = {}
    resKey = ""
    for versKey in dicoVersions:
        if versKey.strip() == call.strip():
            return(versKey)
        # vers = dicoVersions[versKey]
    #     if (vers["call"].strip() == call.strip()):
    #         res = vers
    #         resKey = versKey
    # return(resKey)

def findTest(fileName, dicoTests):
    res = {}
    resKey = ""
    listNb = re.findall(r'\d+', fileName)
    if listNb != []:
        nb = listNb[-1]
    else:
        nb = 0
    for testKey in dicoTests:
        test = dicoTests[testKey]
        if (test["file"].strip() == fileName.strip()):
            res = test
            resKey = testKey
            return(resKey)
        if (test["file"].strip().replace("XX", str(nb)) == fileName.strip()):
            res = test
            resKey = testKey
            return(resKey)


def printLatexMatrix(matrix):
    return(tabulate(matrix[1:], matrix[0], tablefmt="latex"))

def pprintMatrix(matrix):
    lm = len(matrix[0])-1
    table = Texttable()
    # table.set_cols_align(["l", "r", "c"])
    # table.set_deco(Texttable.HEADER)
    table.set_deco(Texttable.BORDER | Texttable.HEADER)
    table.set_precision(2)
    table.set_cols_width([firstWidth]+ ([width]*lm))
    table.set_cols_align(["l"] + (["c"]*lm))
    table.set_cols_dtype(['t'] +  # text 
                         (['t']*lm)) # automatic
    # table.set_cols_valign(["t", "m", "b"])
    table.add_rows(matrix)
    return(table.draw())

def prettyFloat(f):
    return("%.2E" % f)

def extractResults(dicoV, sortedV, dicoT, keyT, disp=None):
    # First column of the line:
    res = [keyT]
    for keyV in sortedV:
        versionDico = dicoV[keyV]
        versionBenchs = versionDico["benchs"]
        found = False
        for bench in versionBenchs:
            if (not(found) and
                versionBenchs[bench]["file"].strip() == dicoT[keyT]["file"].strip()):
                #res.append((versionBenchs[bench]["time"], versionBenchs[bench]["nbExplo"]))
                if versionBenchs[bench]["killed"] != "":
#                    res.append(">(" + prettyFloat(versionBenchs[bench]["time"]) + ")")
                    res.append(">(%s)" % versionBenchs[bench]["killed"])
                elif versionBenchs[bench]["res"] != dicoT[keyT]["res"]:
                    res.append("> X <")
                elif versionBenchs[bench]["new"]:
                    if disp:
                        res.append("->" + prettyFloat(versionBenchs[bench]["nbExplo"]) + "<-")
                    else:
                        res.append("->" + prettyFloat(versionBenchs[bench]["time"]) + "<-")
                elif dateutil.parser.parse(versionBenchs[bench]["date"]) > datetime.now() + timedelta(hours=-2):
                    if disp:
                        res.append("[" + prettyFloat(versionBenchs[bench]["nbExplo"]) + "]")
                    else:
                        res.append("[" + prettyFloat(versionBenchs[bench]["time"]) + "]")
                else:
                    if disp:
                        res.append(prettyFloat(versionBenchs[bench]["nbExplo"]))
                    else:
                        res.append(prettyFloat(versionBenchs[bench]["time"]))
                found = True
        if not(found):
            res.append(".")
    return(res)

def cmpGraph(ex1, ex2):
    if "Graph" in ex1 and "Graph" in ex2:
        n1 = (int(ex1.split("Graph_")[1].split("_par")[0]))
        n2 = (int(ex2.split("Graph_")[1].split("_par")[0]))
        return(cmp(n1,n2))
    else:
        return(cmp(ex1,ex2))

def fromVersToTests(dicoVersions, dicoTests, toLatex=False, vers="all", tests="all", disp=None):
    sortedVersions = ['none', 'new', 'old']
    listTestsKey = sorted(dicoTests.keys(), cmp = cmpGraph)
    listTestsFile = map(lambda x: dicoTests[x]['file'], listTestsKey)
    # first line of the matrix:
    fstLine = [" / "] + sortedVersions
    matrix = [fstLine]
    for i in range(len(listTestsFile)):
        if tests=="all" or (not("old" in listTestsKey[i])):
            keyTest = listTestsKey[i]
            fileName = listTestsFile[i]
            listResults = extractResults(dicoVersions, sortedVersions, dicoTests, keyTest, disp=disp)
            matrix.append(listResults)
    if toLatex:
        return(printLatexMatrix(matrix))
    else:
        return(pprintMatrix(matrix))

def setNoNew(dico):
    for versKey in dico:
        for testKey in dico[versKey]["benchs"]:
            dico[versKey]["benchs"][testKey]["new"] = False
    return(dico)

def filterData(path, dico):
    fileName = path.split("/")[-1]
    resKey = findTest(fileName, dico)
    if resKey == None or resKey == "":
        return(False)
    else:
        return(True)
