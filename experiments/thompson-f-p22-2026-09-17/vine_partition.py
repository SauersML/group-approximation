#!/usr/bin/env python3
"""Thin optimal families are invisible to generic cylinder refinement: the X_1 = S(3->2) test case.

For X_1 = {x_0, x_1} in the tuple model (3 roots -> 2 roots), the finite family
A_D = {(L_i, leaf, R_j) : i + j = D} (L = left vine, R = right vine) has
|X_1 A_D| = D + 2 and |A_D| = D + 1, so h(X_1) = 1.  These sets have Boltzmann mass 4^-D.

This script builds the cylinder partition that resolves exactly the vine cells (entry 1 refined to
LEAF / caret, entry 0 refined along the left vine, entry 2 refined along the right vine with the giant
at its end) to depth D, with O(D^2) cells, and evaluates R(P) with adaptive_limit.run.
Usage: vine_partition.py D1,D2,...
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_limit as al

STAR, LEAF, GIANT = '*', 0, 'G'


def left_open(t, depth, D):
    """t is (((*, .), .), .) pattern: return path of the STAR to refine, or None."""
    path = ()
    while True:
        if t == STAR:
            return path if depth < D else None
        if t == LEAF:
            return None
        a, b = t
        if b == STAR:
            return path + (1,)
        if b != LEAF:
            return None
        t, path, depth = a, path + (0,), depth + 1


def right_open(t, depth, D):
    path = ()
    while True:
        if t == GIANT:
            return path if depth < D else None
        if t in (STAR, LEAF):
            return None
        a, b = t
        if a == STAR:
            return path + (0,)
        if a != LEAF:
            return None
        t, path, depth = b, path + (1,), depth + 1


def crit_vine(D):
    def crit(cell):
        t0, t1, t2 = cell
        if not al.ll.has_giant(t2):
            return None
        if t1 == STAR:
            return (1, ())
        if t1 != LEAF:
            return None
        p = left_open(t0, 0, D)
        if p is not None:
            return (0, p)
        p = right_open(t2, 0, D)
        if p is not None:
            return (2, p)
        return None
    return crit


if __name__ == "__main__":
    for D in map(int, sys.argv[1].split(',')):
        t0 = time.time()
        print(f"vine depth {D}: ", end='', flush=True)
        al.run(3, 2, crit_vine(D))
        print(f"  (D+2)/(D+1) = {(D + 2) / (D + 1):.6f} elapsed {time.time() - t0:.1f}s", flush=True)
