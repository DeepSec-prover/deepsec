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
    'PA_ANO_nd_2': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_2.txt', 'cat': 12, 'det' : False},
    'PA_ANO_nd_3': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_3.txt', 'cat': 12, 'det' : False},
    'PA_ANO_nd_4': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_4.txt', 'cat': 12, 'det' : False},
    'PA_ANO_nd_5': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_5.txt', 'cat': 12, 'det' : False},
    'PA_ANO_nd_6': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_6.txt', 'cat': 12, 'det' : False},
    'feldhofer_plus_2': {'res': True, 'name': ' ', 'file': 'feldhofer_plus_2.txt', 'cat': 12, 'det' : False},
    'PA_UK_nd_2': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_2.txt', 'cat': 12, 'det' : False},
    'PA_UK_nd_3': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_3.txt', 'cat': 12, 'det' : False},
    'BAC_FR_plus_2': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_2.txt', 'cat': 12, 'det' : False},
    'BAC_FR_plus_3': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_3.txt', 'cat': 12, 'det' : False},
    'BAC_plus_2': {'res': True, 'name': ' ', 'file': 'BAC_plus_2.txt', 'cat': 12, 'det' : False},
    'PA_ANO_nd_7': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_7.txt', 'cat': 12, 'det' : False},
    'BAC_plus_3': {'res': True, 'name': ' ', 'file': 'BAC_plus_3.txt', 'cat': 12, 'det' : False},
    'PA_UK_nd_4': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_4.txt', 'cat': 12, 'det' : False},
    'BAC_plus_4': {'res': True, 'name': ' ', 'file': 'BAC_plus_4.txt', 'cat': 12, 'det' : False},
    'BAC_FR_plus_4': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_4.txt', 'cat': 12, 'det' : False},
    'feldhofer_plus_3': {'res': True, 'name': ' ', 'file': 'feldhofer_plus_3.txt', 'cat': 12, 'det' : False},
    'PA_ANO_nd_8': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_8.txt', 'cat': 12, 'det' : False},
    'feldhofer_plus_6': {'res': True, 'name': ' ', 'file': 'feldhofer_plus_6.txt', 'cat': 12, 'det' : False},
    'feldhofer_plus_5': {'res': True, 'name': ' ', 'file': 'feldhofer_plus_5.txt', 'cat': 12, 'det' : False},
    'feldhofer_plus_4': {'res': True, 'name': ' ', 'file': 'feldhofer_plus_4.txt', 'cat': 12, 'det' : False},
    'BAC_FR_plus_5': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_5.txt', 'cat': 12, 'det' : False},
    'BAC_FR_plus_6': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_6.txt', 'cat': 12, 'det' : False},
    'BAC_FR_plus_7': {'res': False, 'name': ' ', 'file': 'BAC_FR_plus_7.txt', 'cat': 12, 'det' : False},
    'BAC_plus_6': {'res': True, 'name': ' ', 'file': 'BAC_plus_6.txt', 'cat': 12, 'det' : False},
    'BAC_plus_7': {'res': True, 'name': ' ', 'file': 'BAC_plus_7.txt', 'cat': 12, 'det' : False},
    'BAC_plus_5': {'res': True, 'name': ' ', 'file': 'BAC_plus_5.txt', 'cat': 12, 'det' : False},
    'BAC_equ_4': {'res': True, 'name': ' ', 'file': 'BAC_equ_4.txt', 'cat': 12},
    'PA_ANO_nd_11': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_11.txt', 'cat': 12},
    'PA_ANO_nd_10': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_10.txt', 'cat': 12},
    'PA_ANO_nd_9': {'res': True, 'name': ' ', 'file': 'PA_ANO_nd_9.txt', 'cat': 12},
    'PA_UK_nd_5': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_5.txt', 'cat': 12},
    'PA_ANO_d_10': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_10.txt', 'cat': 12},
    'PA_ANO_d_8': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_8.txt', 'cat': 12},
    'PA_ANO_d_9': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_9.txt', 'cat': 12},
    'PA_ANO_d_2': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_2.txt', 'cat': 12},
    'PA_ANO_d_3': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_3.txt', 'cat': 12},
    'PA_ANO_d_6': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_6.txt', 'cat': 12},
    'PA_ANO_d_7': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_7.txt', 'cat': 12},
    'PA_ANO_d_4': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_4.txt', 'cat': 12},
    'PA_ANO_d_5': {'res': True, 'name': ' ', 'file': 'PA_ANO_d_5.txt', 'cat': 12},
    'PA_UK_nd_8': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_8.txt', 'cat': 12},
    'PA_UK_nd_6': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_6.txt', 'cat': 12},
    'PA_UK_nd_7': {'res': True, 'name': ' ', 'file': 'PA_UK_nd_7.txt', 'cat': 12},
    'feldhofer_ANO_d_3': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_d_3.txt', 'cat': 12}, 'feldhofer_ANO_d_2': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_d_2.txt', 'cat': 12}, 'feldhofer_ANO_d_6': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_d_6.txt', 'cat': 12}, 'feldhofer_ANO_d_5': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_d_5.txt', 'cat': 12}, 'feldhofer_ANO_d_4': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_d_4.txt', 'cat': 12},
    'feldhofer_ANO_2': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_2.txt', 'cat': 12}, 'feldhofer_ANO_3': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_3.txt', 'cat': 12},
    'feldhofer_ANO_4': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_4.txt', 'cat': 12},
    'feldhofer_ANO_5': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_5.txt', 'cat': 12},
    'feldhofer_ANO_6': {'res': True, 'name': ' ', 'file': 'feldhofer_ANO_6.txt', 'cat': 12}
}
def get_versDico():
    return(DICO)

def get_testsDico():
    return(TESTS)
