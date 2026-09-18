"""Enumerate the inclusion-maximal non-(1/2)-balanced collections of subsets of a k-set A.

Duality (Hahn-Banach / LP, see the research node): a collection Y of subsets of A is NOT
eps-balanced iff there are probability vectors alpha, beta on A with
    alpha(P) - beta(P) > eps   for every P in Y.
Every inclusion-maximal such Y equals Y_w = {P : w(P) > eps} for a w = alpha - beta off all
hyperplanes w(P) = eps, i.e. Y is the in-set of an open cell of the arrangement.
We enumerate open cells by DFS with an LP (maximize slack delta) at every node.
Pictures are bitmasks over A (bit i = element i of A).
"""
import itertools
import json
import sys

import numpy as np
from scipy.optimize import linprog


def lp_slack(k, ins, outs, eps):
    # variables: alpha[0..k-1], beta[0..k-1], delta ; maximize delta
    nv = 2 * k + 1
    A_ub, b_ub = [], []
    for P in ins:  # -(alpha-beta)(P) + delta <= -eps
        row = [0.0] * nv
        for i in range(k):
            if P >> i & 1:
                row[i] -= 1
                row[k + i] += 1
        row[-1] = 1
        A_ub.append(row)
        b_ub.append(-eps)
    for P in outs:  # (alpha-beta)(P) + delta <= eps
        row = [0.0] * nv
        for i in range(k):
            if P >> i & 1:
                row[i] += 1
                row[k + i] -= 1
        row[-1] = 1
        A_ub.append(row)
        b_ub.append(eps)
    A_eq = [[1.0] * k + [0.0] * k + [0.0], [0.0] * k + [1.0] * k + [0.0]]
    b_eq = [1, 1]
    bounds = [(0, 1)] * (2 * k) + [(None, 1)]
    c = [0.0] * (2 * k) + [-1.0]
    r = linprog(c, A_ub=A_ub or None, b_ub=b_ub or None, A_eq=A_eq, b_eq=b_eq,
                bounds=bounds, method="highs")
    if r.status != 0:
        return -1.0, None
    return -r.fun, r.x


def cells(k, eps=0.5, tol=1e-9):
    pics = list(range(1, (1 << k) - 1))  # the empty set and A are never in Y (w(A)=0)
    found = []

    def dfs(i, ins, outs):
        if i == len(pics):
            found.append(tuple(ins))
            return
        P = pics[i]
        for side in (0, 1):
            ni, no = (ins + [P], outs) if side == 0 else (ins, outs + [P])
            d, _ = lp_slack(k, ni, no, eps)
            if d > tol:
                dfs(i + 1, ni, no)

    dfs(0, [], [])
    return found


def maximal(fams):
    sets = sorted({frozenset(f) for f in fams}, key=len, reverse=True)
    out = []
    for s in sets:
        if not any(s < t for t in out):
            out.append(s)
    return out


def closed_faces(k, eps=0.5, tol=1e-9):
    """In-sets of faces: Y = {P : w(P) >= eps} for some w = alpha - beta.
    DFS: 'in' means w(P) >= eps, 'out' means w(P) <= eps - delta (delta > 0 maximised)."""
    pics = list(range(1, (1 << k) - 1))
    found = []

    def feasible(ins, outs):
        nv = 2 * k + 1
        A_ub, b_ub = [], []
        for P in ins:
            row = [0.0] * nv
            for i in range(k):
                if P >> i & 1:
                    row[i] -= 1
                    row[k + i] += 1
            A_ub.append(row)
            b_ub.append(-eps)
        for P in outs:
            row = [0.0] * nv
            for i in range(k):
                if P >> i & 1:
                    row[i] += 1
                    row[k + i] -= 1
            row[-1] = 1
            A_ub.append(row)
            b_ub.append(eps)
        A_eq = [[1.0] * k + [0.0] * k + [0.0], [0.0] * k + [1.0] * k + [0.0]]
        r = linprog([0.0] * (2 * k) + [-1.0], A_ub=A_ub or None, b_ub=b_ub or None,
                    A_eq=A_eq, b_eq=[1, 1], bounds=[(0, 1)] * (2 * k) + [(None, 1)],
                    method="highs")
        return r.status == 0 and (not outs or -r.fun > tol)

    def dfs(i, ins, outs):
        if i == len(pics):
            found.append(tuple(ins))
            return
        P = pics[i]
        if feasible(ins + [P], outs):
            dfs(i + 1, ins + [P], outs)
        if feasible(ins, outs + [P]):
            dfs(i + 1, ins, outs + [P])

    dfs(0, [], [])
    return found


if __name__ == "__main__" and len(sys.argv) > 2 and sys.argv[2] == "closed":
    k = int(sys.argv[1])
    cs = closed_faces(k)
    mx = maximal(cs)
    print("faces", len(cs), "maximal closed families", len(mx))
    json.dump({"k": k, "eps": 0.5, "closed": True, "n_faces": len(cs),
               "maximal": [sorted(s) for s in mx]}, open(f"families_closed_k{k}.json", "w"))
elif __name__ == "__main__":
    k = int(sys.argv[1])
    cs = cells(k)
    mx = maximal(cs)
    print("open cells", len(cs), "maximal families", len(mx))
    json.dump({"k": k, "eps": 0.5, "n_cells": len(cs),
               "maximal": [sorted(s) for s in mx]}, open(f"families_k{k}.json", "w"))
