#!/usr/bin/env python3
"""Sanity check for factorwise-complete-composition-returns-the-input-energy.

Instance W(n,r): n odd, r even, gcd(n,r)=1. Bits x_0..x_(n-1); constraint i
is violated iff x_i+...+x_(i+r-1) is even. lambda_min = 1/n and the uniform
distribution on optimal assignments violates every constraint with
probability 1/n.

Amplified clauses: T copies; clause f=(f(1),...,f(T)) puts constraint f(j) on
copy j. Tensor-OR energy of data X=(x^1..x^T): mean over f of
[some j has f(j) violated by x^j].

Reducers (classical diagonal testers, completeness error eta=0 by
construction): each clause f gets private proof bits whose honest value is a
fixed function of the clause's data bits. Every output term reads at most k0
bits among the clause's data bits and its own proof bits and penalizes exactly
the local patterns that never occur in an honest configuration (data
satisfying every factor f(j) on copy j, plus the honest proof). Hence
factorwise completeness holds exactly.

The theorem predicts lambda_min(H') <= k0/(r n) for every such reducer and
every clause list, independent of T. The script computes lambda_min(H')
exactly and also the explicit fake-proof average of the proof.
"""
import itertools
import math
import random
import sys

import numpy as np


def parity_window(x, i, n, r):
    return sum(x[(i + s) % n] for s in range(r)) % 2


def instance_checks(n, r):
    energies = []
    viol_counts = np.zeros(n)
    best = None
    opt = []
    for bits in itertools.product((0, 1), repeat=n):
        v = [i for i in range(n) if parity_window(bits, i, n, r) == 0]
        energies.append(len(v))
    best = min(energies)
    for idx, bits in enumerate(itertools.product((0, 1), repeat=n)):
        if energies[idx] == best:
            opt.append(bits)
            for i in range(n):
                if parity_window(bits, i, n, r) == 0:
                    viol_counts[i] += 1
    probs = viol_counts / len(opt)
    return best / n, probs, opt


def build_reducer(n, r, T, clauses, k0, nproof, nterms, rng):
    """Return per-clause tables: energy minimized over proofs, indexed by the
    clause's T*r data bits (copy j bits in window order)."""
    tables = []
    raw = []
    for f in clauses:
        nd = T * r
        # honest proof: random mixture of factor parities, ANDs and XORs of data bits
        funcs = []
        for p in range(nproof):
            kind = rng.randrange(3)
            if kind == 0:
                j = rng.randrange(T)
                funcs.append(("par", j))
            elif kind == 1:
                a, b = rng.sample(range(nd), 2)
                funcs.append(("and", a, b))
            else:
                sub = rng.sample(range(nd), rng.randrange(1, nd + 1))
                funcs.append(("xor", tuple(sub)))

        def proof_of(y, funcs=funcs):
            out = []
            for fn in funcs:
                if fn[0] == "par":
                    j = fn[1]
                    out.append(sum(y[j * r + s] for s in range(r)) % 2)
                elif fn[0] == "and":
                    out.append(y[fn[1]] & y[fn[2]])
                else:
                    out.append(sum(y[s] for s in fn[1]) % 2)
            return tuple(out)

        honest = []
        for y in itertools.product((0, 1), repeat=nd):
            if all(sum(y[j * r + s] for s in range(r)) % 2 == 1 for j in range(T)):
                honest.append(y + proof_of(y))
        honest = np.array(honest, dtype=np.int64)
        nb = nd + nproof
        terms = []
        # structured terms: factor-parity flag checks when locality allows
        for p, fn in enumerate(funcs):
            if fn[0] == "par" and r + 1 <= k0:
                terms.append(tuple(list(range(fn[1] * r, fn[1] * r + r)) + [nd + p]))
        while len(terms) < nterms:
            terms.append(tuple(sorted(rng.sample(range(nb), min(k0, nb)))))
        weights = np.array([rng.random() + 0.1 for _ in terms])
        weights /= weights.sum()
        # forbidden-pattern tables
        allcfg = np.array(list(itertools.product((0, 1), repeat=nb)), dtype=np.int64)
        energy = np.zeros(len(allcfg))
        for w, S in zip(weights, terms):
            allowed = set(map(tuple, honest[:, list(S)]))
            pats = allcfg[:, list(S)]
            bad = np.array([tuple(p) not in allowed for p in pats])
            energy += w * bad
        energy = energy.reshape(2 ** nd, 2 ** nproof)
        tables.append(energy.min(axis=1))
        raw.append((energy, weights, terms, proof_of))
    return tables, raw


def data_index(X, f, n, r, T):
    idx = 0
    for j in range(T):
        for s in range(r):
            idx = 2 * idx + X[j][(f[j] + s) % n]
    return idx


def run(n, r, T, k0, nclauses, nproof, nterms, seed):
    rng = random.Random(seed)
    lam, probs, opt = instance_checks(n, r)
    assert abs(lam - 1 / n) < 1e-12, lam
    assert np.allclose(probs, 1 / n), probs
    clauses = [tuple(rng.randrange(n) for _ in range(T)) for _ in range(nclauses)]
    tables, raw = build_reducer(n, r, T, clauses, k0, nproof, nterms, rng)
    # exact lambda_min(H') and tensor-OR energy
    best_red = math.inf
    best_or = math.inf
    for flat in itertools.product((0, 1), repeat=n * T):
        X = [flat[j * n:(j + 1) * n] for j in range(T)]
        e = sum(tables[c][data_index(X, f, n, r, T)] for c, f in enumerate(clauses)) / nclauses
        best_red = min(best_red, e)
        eo = sum(any(parity_window(X[j], f[j], n, r) == 0 for j in range(T)) for f in clauses) / nclauses
        best_or = min(best_or, eo)
    # fake-proof average of the proof (Section 2): equal copies x, flip a uniform
    # qubit of each violated factor, honest proof for the flipped data, average
    tot = 0.0
    for x in opt:
        X = [x] * T
        for c, f in enumerate(clauses):
            energy, weights, terms, proof_of = raw[c]
            viol = [j for j in range(T) if parity_window(x, f[j], n, r) == 0]
            acc = 0.0
            for choice in itertools.product(range(r), repeat=len(viol)):
                y = [X[j][(f[j] + s) % n] for j in range(T) for s in range(r)]
                for j, s in zip(viol, choice):
                    y[j * r + s] ^= 1
                pi = proof_of(tuple(y))
                true = [X[j][(f[j] + s) % n] for j in range(T) for s in range(r)]
                pidx = int("".join(map(str, pi)), 2) if pi else 0
                didx = int("".join(map(str, true)), 2)
                acc += energy[didx, pidx]
            tot += acc / (r ** len(viol)) / nclauses
    fake_avg = tot / len(opt)
    bound = k0 / (r * n)
    ok = best_red <= fake_avg + 1e-12 and fake_avg <= bound + 1e-12
    print(f"n={n} r={r} T={T} k0={k0} clauses={nclauses} proofbits={nproof} terms={nterms} seed={seed}: "
          f"lambda(H)={lam:.4f} lambda(tensorOR)={best_or:.4f} lambda(H')={best_red:.4f} "
          f"fake-proof avg={fake_avg:.4f} bound k0/(rn)={bound:.4f} {'OK' if ok else 'VIOLATION'}")
    return ok


if __name__ == "__main__":
    cases = [
        (5, 2, 2, 2, 12, 2, 6),
        (5, 2, 3, 3, 12, 2, 8),
        (5, 4, 2, 5, 10, 3, 8),
        (7, 4, 2, 5, 12, 3, 8),
        (7, 2, 2, 3, 15, 3, 8),
        (5, 4, 3, 5, 8, 2, 8),
    ]
    allok = True
    for seed in range(3):
        for (n, r, T, k0, nc, npf, nt) in cases:
            allok &= run(n, r, T, k0, nc, npf, nt, seed)
    print("ALL OK" if allok else "SOME VIOLATION")
    sys.exit(0 if allok else 1)
