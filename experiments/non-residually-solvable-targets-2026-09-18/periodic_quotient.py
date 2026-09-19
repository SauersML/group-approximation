#!/usr/bin/env python3
"""Periodic fibre quotients N_D for the 32 UNIT words of the (3,1,3) shape.

Usage:  periodic_quotient.py D FAMILY > file.g ;  gap -q file.g
FAMILY is one of Phi3, Phi6, x2+x-1, x2-x-1 (the polynomial e_2 x^2 + e_1 x + e_0 up to sign).
unit-L15.json (next to this script) lists [word, Magnus rewrite as (index, +-1) pairs, e].
N_D = <a_0..a_{D-1} | r'(a_{k}, a_{k+1}, a_{k+2}), k mod D> is the fibre quotient forced on phi(G) when
phi(t)^D centralises phi(a).  The GAP script prints abelian invariants and a Tietze-reduced presentation;
generator names f1, f2, ... are the surviving a_0, a_1, ...  (periodic-quotient-Phi3.txt is D = 3, Phi3.)
"""
import json, os, sys
W = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'unit-L15.json')))
def fam(ev):
    e0, e1, e2 = ev
    s = 1 if e2 > 0 else -1
    a, b = e1 * s, e0 * s
    return {(1, 1): 'Phi3', (-1, 1): 'Phi6', (1, -1): 'x2+x-1', (-1, -1): 'x2-x-1'}[(a, b)]
def gapword(L, D, sh):
    return '*'.join('f.%d^%d' % (((i + sh) % D) + 1, e) for i, e in L)
D = int(sys.argv[1]); which = sys.argv[2]
for s, L, ev in W:
    if fam(ev) != which:
        continue
    rels = ','.join(gapword(L, D, k) for k in range(D))
    print('f:=FreeGroup(%d);; g:=f/[%s];; ' % (D, rels))
    print('Print("%s %s D=%d ", AbelianInvariants(g), " ");' % (s, ev, D))
    print('p:=PresentationFpGroup(g,0);; TzGoGo(p);; h:=FpGroupPresentation(p);; Print(RelatorsOfFpGroup(h),"\\n");')
print('QUIT;')
