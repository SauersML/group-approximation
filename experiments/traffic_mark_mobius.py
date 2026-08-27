#!/usr/bin/env python3
"""Canonical Möbius-sign inequalities for an oriented finite implication table.

This is a proof-discovery utility for the branching-traffic/Markovization route.
For a finite Horn closure system, the closed local stabilizer patterns form a
finite poset.  Simultaneous-fixed-set moments m(C)=Pr[C subseteq H_x] are the
zeta transform of exact pattern probabilities p(B).  Möbius inversion gives
p(B)=sum_C mu(B,C)m(C), so every classical action satisfies p(B)>=0.

The built-in example is the minimal oriented associativity square:
  {g,h}->k, {h,r}->s, {g,s}->t, {k,r}->t.
"""

from itertools import combinations
import argparse
import json


def closure(seed, rules):
    out = set(seed)
    changed = True
    while changed:
        changed = False
        for lhs, rhs in rules:
            if lhs <= out and rhs not in out:
                out.add(rhs)
                changed = True
    return frozenset(out)


def closed_sets(ground, rules):
    pts = list(ground)
    out = []
    for mask in range(1 << len(pts)):
        s = frozenset(pts[i] for i in range(len(pts)) if (mask >> i) & 1)
        if closure(s, rules) == s:
            out.append(s)
    return sorted(out, key=lambda s: (len(s), tuple(sorted(s))))


def anti_exchange(closed, rules):
    ground = set().union(*closed) if closed else set()
    for c in closed:
        outside = list(ground - set(c))
        for i, x in enumerate(outside):
            for y in outside[i + 1:]:
                if x in closure(set(c) | {y}, rules) and y in closure(set(c) | {x}, rules):
                    return False, (c, x, y)
    return True, None


def mobius(closed):
    # mu[(a,b)] for a subseteq b in the closed-set inclusion poset.
    mu = {}
    for a in reversed(closed):
        supers = [b for b in closed if a <= b]
        supers.sort(key=lambda s: (len(s), tuple(sorted(s))))
        for b in supers:
            if a == b:
                mu[(a, b)] = 1
            else:
                mu[(a, b)] = -sum(mu[(a, c)] for c in supers if c < b)
    return mu


def fmt(s):
    return "{" + ",".join(sorted(s)) + "}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=12)
    args = ap.parse_args()

    ground = {"g", "h", "r", "k", "s", "t"}
    rules = [
        (frozenset({"g", "h"}), "k"),
        (frozenset({"h", "r"}), "s"),
        (frozenset({"g", "s"}), "t"),
        (frozenset({"k", "r"}), "t"),
    ]
    closed = closed_sets(ground, rules)
    ae, witness = anti_exchange(closed, rules)
    mu = mobius(closed)

    rows = []
    for b in closed:
        terms = [(a, mu[(b, a)]) for a in closed if b <= a and mu.get((b, a), 0)]
        rows.append((max(abs(c) for _, c in terms), len(terms), b, terms))
    rows.sort(key=lambda x: (-x[0], -x[1], len(x[2]), fmt(x[2])))

    print(json.dumps({
        "ground": sorted(ground),
        "rules": [[sorted(lhs), rhs] for lhs, rhs in rules],
        "closed_sets": len(closed),
        "anti_exchange": ae,
        "anti_exchange_witness": None if witness is None else [fmt(witness[0]), witness[1], witness[2]],
    }, indent=2))
    print("\nCanonical inequalities p(B)=sum_{A>=B} mu(B,A)m(A) >= 0")
    for _, _, b, terms in rows[:args.top]:
        rhs = " ".join(("+" if coeff > 0 else "-") + ("" if abs(coeff) == 1 else str(abs(coeff)) + "*") + f"m{fmt(a)}" for a, coeff in terms)
        print(f"p{fmt(b)} = {rhs.lstrip('+')} >= 0")


if __name__ == "__main__":
    main()
