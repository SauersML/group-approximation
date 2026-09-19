"""Numerical witness for the (I2) route of the corrected transfer lemma.

The corrected lemma (`notes/STEINBERG_SPARE_INDEX_2026-08-15.md` §11.3) replaces
the over-strong hypotheses of `ATLAS_COMPLETENESS_DERIVATION_2026-08-15.md`
Lemma 3.1 with three (St2) instances between strictly shorter objects:

    T := [X, V] = U V U^-1 · [U,Z] · V^-1                             (I2)
    U := [X,Y],  V := [Y,Z],
    hypotheses:  [X,Z] = 1,  [U,V] = 1,  [Z,V] = 1
    conclusion:  T = [U,Z]                      and [Y,V] = 1 is NOT needed.

Algebraically (I2) is `X V X^-1 = U V Z U^-1 Z^-1`, which follows from
`X Y X^-1 = U Y`, `Y Z Y^-1 = V Z` and `[X,Z] = 1` alone.  Then `[U,V] = 1`
collapses `U V U^-1` to `V`, and `V` commuting with both `U` and `Z` makes it
commute with `[U,Z]`, giving `T = [U,Z]`.

This script supplies the two things asked for.

PART A — exhaustive, in `S_5`.  All `120^3 = 1,728,000` ordered triples are
classified by which of the three hypotheses hold, and both `(I2)` and the
conclusion are tested in every cell.  This settles the implications outright
for a group, and — crucially — exhibits cells where a hypothesis fails and the
conclusion breaks, which is what shows each one is load bearing.  It also
isolates the cells where `[Y,V] != 1` yet all three hypotheses hold, giving a
direct witness that `[Y,V]` is not needed.

PART B — the intended root configuration, in `Q`.  For every ordered quadruple
of distinct indices and every coefficient pair, `X = x_il(a)`, `Y = x_lk(1)`,
`Z = x_kj(b)` are built from the verified dictionary and the three hypotheses
are checked to actually hold there, along with both conclusions.

A group identity cannot be established by testing one group, and Part A is not
offered as a proof; it is offered as the missing numerical witness, and as a
refutation test that the identity would have failed had the hypothesis set
been stated wrongly.
"""

import argparse
import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ----------------------------------------------------------------- Part A

def symmetric_group_tables(n):
    perms = [tuple(p) for p in itertools.permutations(range(n))]
    index = {p: i for i, p in enumerate(perms)}
    size = len(perms)
    mul = np.empty((size, size), dtype=np.int16)
    for a, pa in enumerate(perms):
        for b, pb in enumerate(perms):
            mul[a, b] = index[tuple(pa[pb[i]] for i in range(n))]
    inv = np.empty(size, dtype=np.int16)
    for a, pa in enumerate(perms):
        q = [0] * n
        for i, v in enumerate(pa):
            q[v] = i
        inv[a] = index[tuple(q)]
    identity = index[tuple(range(n))]
    return mul, inv, identity, size


def part_a(n=5, chunk=200000):
    mul, inv, e, size = symmetric_group_tables(n)
    print("PART A: exhaustive over S_%d, |G| = %d, triples = %d"
          % (n, size, size ** 3))

    def M(a, b):
        return mul[a, b]

    def comm(a, b):
        return M(M(a, b), M(inv[a], inv[b]))

    # cells: (hXZ, hUV, hZV) -> [i2_ok, i2_bad, concl_ok, concl_bad,
    #                            yv_free_ok, yv_free_bad]
    cells = {}
    total = size ** 3
    xs = np.arange(size, dtype=np.int16)
    for start in range(0, size * size, chunk):
        stop = min(start + chunk, size * size)
        flat = np.arange(start, stop)
        X = (flat // size).astype(np.int16)
        Y = (flat % size).astype(np.int16)
        for Zv in range(size):
            Z = np.full(X.shape, Zv, dtype=np.int16)
            U = comm(X, Y)
            V = comm(Y, Z)
            T = comm(X, V)
            W = comm(U, Z)

            hXZ = comm(X, Z) == e
            hUV = comm(U, V) == e
            hZV = comm(Z, V) == e
            hYV = comm(Y, V) == e

            # (I2): T == U V U^-1 [U,Z] V^-1
            rhs = M(M(M(M(U, V), inv[U]), W), inv[V])
            i2 = T == rhs
            concl = T == W

            for key in itertools.product((False, True), repeat=3):
                mask = ((hXZ == key[0]) & (hUV == key[1]) & (hZV == key[2]))
                if not mask.any():
                    continue
                slot = cells.setdefault(key, np.zeros(6, dtype=np.int64))
                slot[0] += int((mask & i2).sum())
                slot[1] += int((mask & ~i2).sum())
                slot[2] += int((mask & concl).sum())
                slot[3] += int((mask & ~concl).sum())
                free = mask & ~hYV
                slot[4] += int((free & concl).sum())
                slot[5] += int((free & ~concl).sum())
    del xs

    print()
    print("%-22s %12s %10s %10s %10s %10s" %
          ("[X,Z] [U,V] [Z,V]", "triples", "(I2) ok", "(I2) BAD",
           "T=[U,Z]", "T!=[U,Z]"))
    seen = 0
    for key in sorted(cells, reverse=True):
        s = cells[key]
        n_cell = int(s[0] + s[1])
        seen += n_cell
        print("%-22s %12d %10d %10d %10d %10d"
              % ("  ".join("T" if k else "." for k in key),
                 n_cell, s[0], s[1], s[2], s[3]))
    assert seen == total, (seen, total)

    print()
    ok = True
    for key, s in cells.items():
        hXZ, hUV, hZV = key
        if hXZ and s[1]:
            print("VIOLATION: (I2) failed with [X,Z]=1 in cell", key)
            ok = False
        if not hXZ and s[1] == 0 and s[0] + s[1] > 0:
            pass  # (I2) may still hold by accident; not a violation
        if hXZ and hUV and hZV and s[3]:
            print("VIOLATION: conclusion failed with all three hypotheses",
                  key)
            ok = False
    print("(I2) holds in EVERY triple with [X,Z]=1:",
          all(not k[0] or v[1] == 0 for k, v in cells.items()))
    print("conclusion holds in EVERY triple with all three hypotheses:",
          all(not (k[0] and k[1] and k[2]) or v[3] == 0
              for k, v in cells.items()))

    print()
    print("Load-bearing check -- a hypothesis is load bearing if dropping it")
    print("admits counterexamples to the conclusion:")
    for key in [(False, True, True), (True, False, True), (True, True, False)]:
        s = cells.get(key)
        missing = ["[X,Z]", "[U,V]", "[Z,V]"][[not k for k in key].index(True)]
        if s is None:
            print("  drop %-6s : cell empty in S_%d" % (missing, n))
        else:
            print("  drop %-6s : %d triples, %d violate the conclusion  %s"
                  % (missing, s[2] + s[3], s[3],
                     "<-- load bearing" if s[3] else "<-- no counterexample"))

    s = cells.get((True, True, True))
    if s is not None:
        print()
        print("[Y,V] is NOT needed: among triples satisfying all three")
        print("  hypotheses but with [Y,V] != 1:  %d triples, %d violate"
              % (s[4] + s[5], s[5]))
    return ok


# ----------------------------------------------------------------- Part B

def part_b():
    from atlas_kernel_collision_enumerator import evaluate_word
    from atlas_relator_rank5_dictionary import (
        COEFF_LETTERS, leavitt_equal, rank5_word)
    from atlas_two_chart_search import commutator, inverse, product, reduce_word

    memo = {}

    def x(i, j, b):
        return rank5_word(i, j, b, memo)[0]

    def is_one(word):
        word = reduce_word(word)
        return (not word) or leavitt_equal(
            evaluate_word(word), {((), ()): 1})

    counts = dict(checked=0, hXZ=0, hUV=0, hZV=0, hYV=0, i2=0, concl=0)
    for i, j, k, l in itertools.permutations(range(1, 6), 4):
        for a, b in itertools.product(COEFF_LETTERS, repeat=2):
            X, Y, Z = x(i, l, a), x(l, k, "1"), x(k, j, b)
            U = reduce_word(commutator(X, Y))
            V = reduce_word(commutator(Y, Z))
            T = reduce_word(commutator(X, V))
            W = reduce_word(commutator(U, Z))

            counts["checked"] += 1
            counts["hXZ"] += is_one(commutator(X, Z))
            counts["hUV"] += is_one(commutator(U, V))
            counts["hZV"] += is_one(commutator(Z, V))
            counts["hYV"] += is_one(commutator(Y, V))

            rhs = product(product(product(U, V), inverse(U)),
                          product(W, inverse(V)))
            counts["i2"] += is_one(product(T, inverse(reduce_word(rhs))))
            counts["concl"] += is_one(product(T, inverse(W)))

    print("PART B: the intended root configuration, evaluated in Q")
    print("  quadruples x coefficient pairs:", counts["checked"])
    for name, label in (("hXZ", "[X,Z] = 1"), ("hUV", "[U,V] = 1"),
                        ("hZV", "[Z,V] = 1"), ("hYV", "[Y,V] = 1")):
        print("    %-12s holds in %d of %d"
              % (label, counts[name], counts["checked"]))
    print("    (I2) holds in       %d of %d" % (counts["i2"],
                                                counts["checked"]))
    print("    T = [U,Z] holds in  %d of %d" % (counts["concl"],
                                                counts["checked"]))
    return counts["i2"] == counts["checked"] == counts["concl"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=5)
    parser.add_argument("--skip-a", action="store_true")
    parser.add_argument("--skip-b", action="store_true")
    args = parser.parse_args()

    ok = True
    if not args.skip_a:
        ok &= part_a(args.degree)
        print()
    if not args.skip_b:
        ok &= part_b()
    print()
    print("NOTE: Part A settles the implications for one group exhaustively;")
    print("it is a witness and a refutation test, not a proof of a group")
    print("identity.  Part B confirms the hypotheses really hold in the")
    print("configuration the derivation uses.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
