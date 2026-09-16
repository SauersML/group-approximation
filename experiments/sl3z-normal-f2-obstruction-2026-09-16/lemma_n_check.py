#!/usr/bin/env python3
"""Lemma N check (artifact research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md, Section 3).

For the elementary Nielsen automorphisms sigma, iota, tau of F(a,b), and for
random products of them, verify that alpha(c) is conjugate to c or c^-1,
where c = [a,b] = a b a^-1 b^-1. Also record that c and c^-1 are not conjugate,
so the orbit {[c], [c^-1]} really has two elements.

The generator checks are the proof content; the random products only test the
composition bookkeeping. Words are lists of nonzero ints: 1 = a, 2 = b,
negative = inverse. Single-threaded, fixed seed, runs in about a second.
"""
import random

def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out

def inv(w):
    return [-x for x in reversed(w)]

def cyc(w):
    w = red(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w

def conj_eq(u, v):
    u, v = cyc(u), cyc(v)
    if len(u) != len(v):
        return False
    if not u:
        return True
    return any(u[i:] + u[:i] == v for i in range(len(u)))

def apply(alpha, w):
    out = []
    for x in w:
        img = alpha[abs(x)]
        out.extend(img if x > 0 else inv(img))
    return red(out)

def compose(alpha, beta):  # (alpha o beta)(x) = alpha(beta(x))
    return {1: apply(alpha, beta[1]), 2: apply(alpha, beta[2])}

C = [1, 2, -1, -2]
GENS = {
    "sigma": {1: [2], 2: [1]},
    "iota": {1: [-1], 2: [2]},
    "tau": {1: [1, 2], 2: [2]},
}

def status(alpha):
    img = apply(alpha, C)
    if conj_eq(img, C):
        return +1
    if conj_eq(img, inv(C)):
        return -1
    return 0

def main():
    print("c conjugate to c^-1:", conj_eq(C, inv(C)))
    for name, g in GENS.items():
        print(name, "image of c:", apply(g, C), "class sign:", status(g))
    # inverses of generators as automorphisms
    INV = {
        "sigma^-1": {1: [2], 2: [1]},
        "iota^-1": {1: [-1], 2: [2]},
        "tau^-1": {1: [1, -2], 2: [2]},
    }
    for name, g in INV.items():
        print(name, "class sign:", status(g))
    rng = random.Random(20260916)
    pool = list(GENS.values()) + list(INV.values())
    fails = 0
    trials = 2000
    for _ in range(trials):
        alpha = {1: [1], 2: [2]}
        for _ in range(rng.randint(1, 12)):
            alpha = compose(alpha, rng.choice(pool))
        if status(alpha) == 0:
            fails += 1
    print("random products:", trials, "failures:", fails)
    print("OK" if fails == 0 else "FAIL")

if __name__ == "__main__":
    main()
