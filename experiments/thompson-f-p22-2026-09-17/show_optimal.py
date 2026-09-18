#!/usr/bin/env python3
"""Print the optimal depth-h profile set of local_limit.py.  Usage: show_optimal.py n k h"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import local_limit as ll


def s(p):
    if p == '*':
        return '*'
    if p == 0:
        return '.'
    if p == 'G':
        return 'G'
    return '(' + s(p[0]) + s(p[1]) + ')'


n, k, h = map(int, sys.argv[1:4])
left, classes, ns = ll.build(n, k, h)
r, A = ll.optimize(left, classes, n - k)
print("R_h =", r, float(r), "| chosen", len(A), "of", len(left))
tot = sum(left.values())
print("mass fraction chosen:", float(sum(left[a] for a in A) / tot))
print("excluded profiles:")
Aset = set(A)
for a in sorted(left, key=str):
    if a not in Aset:
        print(' '.join(s(p) for p in a), left[a])
