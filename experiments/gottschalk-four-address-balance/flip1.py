#!/usr/bin/env python3
"""Single-flip census for binary four-address rules.

Addresses 0..3 stand for memory elements m_0..m_3 of a group G.  The ordered pair
(i, j), i != j, stands for the quotient m_i^-1 m_j.  A flip of x at h changes the pattern
at the output sites h m_i^-1, where coordinate i reads x(h) and coordinate j != i reads
x(h m_i^-1 m_j) = x(h q(i,j)).  So the flip is invisible iff there are values on the sites
h q(i,j) whose context at every i is blind in coordinate i.  Sites coincide exactly when the
quotients coincide in G, i.e. along the quotient partition of the 12 ordered pairs.

A quotient partition is admissible if it is stable under the reversal (i,j) -> (j,i)
(inversion) and never merges (i,j) with (i,k) or (j,i) with (k,i) for j != k
(those force m_j = m_k).  This script enumerates admissible partitions, and for every
rule class decides whether the single-flip CSP is satisfiable on each partition.

Output (JSON): for every unbalanced rule class passing the constant test mu(0000) != mu(1111),
the list of admissible partitions on which no invisible single flip exists.
"""
import itertools, json, sys

PAIRS = [(i, j) for i in range(4) for j in range(4) if i != j]
PIDX = {p: k for k, p in enumerate(PAIRS)}
REV = [PIDX[(j, i)] for (i, j) in PAIRS]


def bit(x, i):
    return (x >> i) & 1


def rule_eval(mu, bits):
    """mu is a 16-bit table indexed by x = sum bits[i] << i."""
    x = bits[0] | (bits[1] << 1) | (bits[2] << 2) | (bits[3] << 3)
    return (mu >> x) & 1


def blind_contexts(mu, i):
    """Contexts of coordinate i (as dict j -> bit for j != i) where mu is blind in i."""
    out = []
    others = [j for j in range(4) if j != i]
    for vals in itertools.product((0, 1), repeat=3):
        b0 = [0, 0, 0, 0]
        for j, v in zip(others, vals):
            b0[j] = v
        b1 = list(b0)
        b1[i] = 1
        if rule_eval(mu, b0) == rule_eval(mu, b1):
            out.append(dict(zip(others, vals)))
    return out


def admissible_partitions():
    """Set partitions of the 12 pairs, stable under REV, with row/column separation."""
    n = len(PAIRS)
    results = []
    label = [-1] * n

    def ok_merge(a, b):
        (i, j), (k, l) = PAIRS[a], PAIRS[b]
        if i == k and j != l:
            return False
        if j == l and i != k:
            return False
        return True

    def consistent(lbl):
        # row/column separation inside classes, and REV-stability of the labelling
        classes = {}
        for p, c in enumerate(lbl):
            if c >= 0:
                classes.setdefault(c, []).append(p)
        for c, mem in classes.items():
            for a, b in itertools.combinations(mem, 2):
                if not ok_merge(a, b):
                    return False
        return True

    # enumerate restricted growth strings, then filter REV-stability at the end
    def rec(p, nclasses):
        if p == n:
            # REV stability: p~q iff REV p ~ REV q
            for a in range(n):
                for b in range(a + 1, n):
                    if (label[a] == label[b]) != (label[REV[a]] == label[REV[b]]):
                        return
            results.append(tuple(label))
            return
        for c in range(nclasses + 1):
            label[p] = c
            # prune: row/column separation with earlier members of class c
            good = True
            for q in range(p):
                if label[q] == c and not ok_merge(q, p):
                    good = False
                    break
            if good:
                rec(p + 1, max(nclasses, c + 1))
        label[p] = -1

    rec(0, 0)
    return results


def csp_satisfiable(ins, lbl):
    """ins[i]: blind contexts of coordinate i; lbl: class label of each pair."""
    assign = {}

    def rec(i):
        if i == 4:
            return True
        for ctx in ins[i]:
            newly = []
            good = True
            for j, v in ctx.items():
                c = lbl[PIDX[(i, j)]]
                if c in assign:
                    if assign[c] != v:
                        good = False
                        break
                else:
                    assign[c] = v
                    newly.append(c)
            if good and rec(i + 1):
                return True
            for c in newly:
                del assign[c]
        return False

    return rec(0)


def canonical_rule(mu):
    """Smallest table under address permutations, input complement, output complement."""
    best = None
    for perm in itertools.permutations(range(4)):
        for inneg in (0, 1):
            for outneg in (0, 1):
                t = 0
                for x in range(16):
                    bits = [bit(x, i) for i in range(4)]
                    y = 0
                    for i in range(4):
                        y |= (bits[perm[i]] ^ inneg) << i
                    v = ((mu >> y) & 1) ^ outneg
                    t |= v << x
                if best is None or t < best:
                    best = t
    return best


def main():
    parts = admissible_partitions()
    sys.stderr.write("admissible partitions: %d\n" % len(parts))
    reps = sorted({canonical_rule(mu) for mu in range(1 << 16)
                   if bin(mu).count("1") != 8})
    sys.stderr.write("unbalanced rule classes: %d\n" % len(reps))
    out = {"partitions": parts, "rules": {}}
    for mu in reps:
        if rule_eval(mu, [0, 0, 0, 0]) == rule_eval(mu, [1, 1, 1, 1]):
            continue  # constant test C1 kills it over every group
        ins = [blind_contexts(mu, i) for i in range(4)]
        fails = [k for k, lbl in enumerate(parts) if not csp_satisfiable(ins, lbl)]
        out["rules"][mu] = fails
    json.dump(out, sys.stdout)


if __name__ == "__main__":
    main()
