#!/usr/bin/python
# -*- coding: iso-8859-1 -*-

DICO = {
    'none' : {
        "name" : "DeepSec without POR (option '-no_por')",
        "call" : "deepsec -no_por",
        "branch" : "",
        "benchs": {
            "TEST": {
                "new" : False,
                "file": "TEST.txt",
                "res" : True,
                "date" : "1263",
                "time": "453",
                "nbExplo" : "4674",
                "fileFrom" : "BENCH.log"
            }
        }
    },
    'old' : {
        "name" : "Old POR for determinate processes only.",
        "call" : "deepsec",
        "branch" : "",
        "benchs": {}
    },
    'new' : {
        "name" : "New Generalized POR",
        "call" : "deepsec -with_por_gen",
        "branch" : "",
        "benchs": {}
    },
}

TESTS = {
    'PA_ANO_nd_2': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_2.txt', 'cat': 12},
    'PA_ANO_nd_3': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_3.txt', 'cat': 12},
    'PA_ANO_nd_4': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_4.txt', 'cat': 12},
    'PA_ANO_nd_5': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_5.txt', 'cat': 12},
    'PA_ANO_nd_6': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_6.txt', 'cat': 12},
    'feldhofer_plus_2': {'res': True, 'name': ' ', 'file': 'feldhofer_plus_2.txt', 'cat': 12},
    'PA_UK_nd_2': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_2.txt', 'cat': 12},
    'PA_UK_nd_3': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_3.txt', 'cat': 12},
    'BAC_FR_plus_2': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_2.txt', 'cat': 12},
    'BAC_FR_plus_3': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_3.txt', 'cat': 12},
    'BAC_plus_2': {'res': True, 'name': ' ', 'file': 'BAC_plus_2.txt', 'cat': 12},
    'PA_ANO_nd_7': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_7.txt', 'cat': 12},
    'BAC_plus_3': {'res': True, 'name': ' ', 'file': 'BAC_plus_3.txt', 'cat': 12},
    'PA_UK_nd_4': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_4.txt', 'cat': 12},
    'BAC_plus_4': {'res': True, 'name': ' ', 'file': 'BAC_plus_4.txt', 'cat': 12}
}

def get_versDico():
    return(DICO)

def get_testsDico():
    return(TESTS)
