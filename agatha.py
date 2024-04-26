
import time
import sys
import csv
import sqlite3
import functools
import itertools
from more_itertools import unique_everseen

from delphin import itsdb, tsql, mrs
from delphin.codecs import simplemrs, mrx, mrsprolog

import ulkb
from ulkb import *
import z3

import mrs_logic
# from mrs_logic.ukb import UKB, UKB_Error
from mrs_logic import parse, Solver

import logging
logging.basicConfig(level=logging.INFO)



ACE_GRAMMAR = "../erg.dat"

# You can set global MRS Logic options in the context.
ctx = mrs_logic.get_current_context()

# to_ulkb() defaults
aty = ulkb.TypeVariable('a')
ctx.options.to_ulkb.drop_evars = False
ctx.options.to_ulkb.universe_type = aty
# ctx.options.to_ulkb.drop_ivars = True
# ctx.options.to_ulkb.drop_uvars = True
ctx.options.to_ulkb.mk_q_exists = '_the_q'

ulkb.settings.serializer.ulkb.show_annotations = True
ulkb.settings.serializer.ulkb.show_types = False
ulkb.settings.serializer.ulkb.omit_labels = False


def take_equivs(n, solutions):
    # print("take_equivs init")
    res, c, U = [], 0, 1000
    while (len(res) < n and c < U):
        try:
            s = next(solutions)
            f = s.to_ulkb()
            ignore = False
            if len(res) == 0:
                res.append(f)
            else:
                for r in res:
                    try:
                        RuleZ3(And(Implies(r,f),Implies(f,r)))
                        ignore = True
                        c += 1
                        break
                    except RuleError as e1:
                        continue
                if not(ignore):
                    res.append(f)
        except StopIteration as e1:
            # print("take_equivs exausted")
            break
        except Exception as e2:
            # print('take_equivs: ', e2)
            pass
    return res


def transform(mrs):
    # mrs = next(parse(txt))
    # print("sentence", txt)
    # print(simplemrs.encode(mrs, indent=True, properties=True))
    solver = Solver(mrs)
    res = take_equivs(1, solver.iterate_solutions())
    return res[0]



## Axioms

txt = ['Someone who lives in Dreadbury Mansion killed Aunt Agatha.',
       'Agatha, the butler, and Charles live in Dreadbury Mansion, and are the only people who live therein.',
       'A killer always hates his victim, and is never richer than his victim.',
       'Charles hates no one that Aunt Agatha hates.',
       'Agatha hates everyone except the butler.',
       'The butler hates everyone not richer than Aunt Agatha.',
       'The butler hates everyone Aunt Agatha hates.',
       'No one hates everyone.',
       'Agatha is not the butler.',
       'Therefore, Agatha killed herself.'] # conjecture

# removing compound Aunt Agatha ~> Agatha  and Dreadbury Mansion ~> Dreadbury

txt = ['Someone who lives in Dreadbury killed Agatha.',
       'Agatha, the butler, and Charles live in Dreadbury, and are the only people who live therein.',
       'A killer always hates his victim, and is never richer than his victim.',
       'Charles hates no one that Agatha hates.',
       'Agatha hates everyone except the butler.',
       'The butler hates everyone not richer than Agatha.',
       'The butler hates everyone Agatha hates.',
       'No one hates everyone.',
       'Agatha is not the butler.',
       'Agatha killed herself.'] # conjecture


ts = itsdb.TestSuite('agatha')
conjecture, theory = None, {}

for row in tsql.select('i-id mrs', ts):
    k = int(row[0])
    v = simplemrs.decode(row[1])
    print(simplemrs.encode(v, properties=False, lnk=True, indent=True))
    
    frm = transform(v)
    if k == 10:
        conjecture = frm
    else:
        print(frm)
        new_axiom(f'ax{k}', frm)

# show_axioms()


# manually rewriting to add the coref of Agatha = herself

# ab   = FunctionType(aty, BoolType())           # a -> bool : *
# aab  = FunctionType(aty, aty, BoolType())      # a -> a -> bool : *
# aaab = FunctionType(aty, aty, aty, BoolType()) # a -> a -> a -> bool : *
# e, x, y, z, v = Variables('e', 'x', 'y', 'z', 'v', aty)

# _kill_v_1 = Constant('_kill_v_1', aaab)
# pron = Constant('pron', ab)
# Agatha = Constant('Agatha', aty)

# conjecture_f = Exists(x, And(pron(x), Exists(y, And(Equal(Agatha,y), Equal(x,y), Exists(z, _kill_v_1(z,y,x))))))
# print('conjecture\n\t',conjecture_f)

try:
    RuleZ3(conjecture)
except RuleError as e:
    print(f'I could not prove\n\t {conjecture}\n')
    sys.exit(1)
else:
    print('I proved it.')
    sys.exit(0)

    
