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
}

def get_versDico():
    return(DICO)

def get_testsDico():
    return(TESTS)
