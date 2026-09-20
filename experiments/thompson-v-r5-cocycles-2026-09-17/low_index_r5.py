#!/usr/bin/env python3
"""Low-index subgroups (Sims) of G0/<<base>>, G0 = <a,b,c | a^2,b^3,(ab)^4,c^2,(ac)^3>.

Thompson's V is infinite and simple, so it has no subgroup of finite index > 1.  Hence any
transitive permutation action of G0/<<base>> on n >= 2 points proves G0/<<base>> != V.  We
enumerate subgroups of index <= N by the standard coset-table backtrack (each subgroup once, with
coset 0 = the subgroup and cosets numbered in definition order), with full HLT relator scanning
for deductions.  Every complete table found is re-verified by evaluating all relators as
permutations.  For each hit we also report which of r5..r8 / (2.3) words fail on it.

usage: low_index_r5.py N base_csv [check_csv]
"""
import sys

import prefix_cocycles as pc

COLS = ["a", "b", "B", "c"]
INV = {0: 0, 1: 2, 2: 1, 3: 3}
CI = {("a", 1): 0, ("a", -1): 0, ("b", 1): 1, ("b", -1): 2, ("c", 1): 3, ("c", -1): 3}


def word_cols(w):
    return [CI[t] for t in w]


def scan_all(T, n_def, rels):
    """Propagate deductions; return False on coincidence (contradiction)."""
    changed = True
    while changed:
        changed = False
        for x in range(n_def):
            for r in rels:
                # forward
                f = x
                i = 0
                L = len(r)
                while i < L:
                    y = T[f][r[i]]
                    if y is None:
                        break
                    f = y
                    i += 1
                if i == L:
                    if f != x:
                        return False
                    continue
                # backward
                bk = x
                j = L - 1
                while j >= i:
                    y = T[bk][INV[r[j]]]
                    if y is None:
                        break
                    bk = y
                    j -= 1
                if j < i:
                    if f != bk:
                        return False
                    continue
                if j == i:
                    g = r[i]
                    # deduce T[f][g] = bk
                    if T[f][g] is not None and T[f][g] != bk:
                        return False
                    if T[bk][INV[g]] is not None and T[bk][INV[g]] != f:
                        return False
                    T[f][g] = bk
                    T[bk][INV[g]] = f
                    changed = True
    return True


def evaluate(T, w, x):
    for col in word_cols(w):
        x = T[x][col]
    return x


def search(N, rels, report):
    n_found = [0]

    def rec(T, n_def):
        # first undefined entry
        for x in range(n_def):
            for g in range(4):
                if T[x][g] is None:
                    break
            else:
                continue
            break
        else:
            report(T, n_def)
            n_found[0] += 1
            return
        gi = INV[g]
        cands = [y for y in range(n_def) if T[y][gi] is None or (y == x and gi == g)]
        if n_def < N:
            cands.append(n_def)
        for y in cands:
            T2 = [row[:] for row in T]
            nd = n_def
            if y == n_def:
                T2.append([None] * 4)
                nd += 1
            if T2[y][gi] is not None and T2[y][gi] != x:
                continue
            T2[x][g] = y
            T2[y][gi] = x
            if scan_all(T2, nd, rels):
                rec(T2, nd)

    rec([[None] * 4], 1)
    return n_found[0]


def main():
    N = int(sys.argv[1])
    base = sys.argv[2].split(",")
    check = sys.argv[3].split(",") if len(sys.argv) > 3 else ["r5", "r6", "r7", "r8"]
    rels = [word_cols(pc.WORDS[nm]) for nm in base]
    hist = {}

    def report(T, n):
        # verify: all columns defined, inverse-consistent, base relators hold everywhere
        for x in range(n):
            for g in range(4):
                assert T[T[x][g]][INV[g]] == x
        for nm in base:
            for x in range(n):
                assert evaluate(T, pc.WORDS[nm], x) == x, nm
        fails = [nm for nm in check if any(evaluate(T, pc.WORDS[nm], x) != x for x in range(n))]
        hist[n] = hist.get(n, 0) + 1
        if n >= 2:
            perm = {g: [T[x][CI[(g, 1)]] for x in range(n)] for g in "abc"}
            print("HIT index", n, "fails", fails, "perms", perm, flush=True)

    total = search(N, rels, report)
    print({"N": N, "base": base, "subgroups_found": total, "by_index": hist})


if __name__ == "__main__":
    main()
