#!/usr/bin/env python3
"""Independent check of a non-doubling witness in the positive monoid M of Thompson's group F.

A witness for a finite set S of normal forms is a finite nonempty set Y of normal forms with
|S Y| < 2|Y|.  This module shares no code with witness_flow.cpp.

* Normal forms are nondecreasing integer tuples (i_1, ..., i_D) standing for x_(i_1)...x_(i_D).
* Products are computed by the rewriting rule x_j x_i = x_i x_(j+1) for i < j.
* selftest() checks that rule against the standard piecewise-linear model of F, composing
  maps so that (g h)(t) = g(h(t)): x_0 is the map with breakpoints (1/2,1/4), (3/4,1/2), and x_n
  is the identity on [0, 1 - 2^-n] and a rescaled copy of x_0 on [1 - 2^-n, 1].  It also checks
  that distinct normal forms of small degree give distinct maps (uniqueness of normal forms).

Usage: verify_witness.py CERT[.gz] MONOMIALS D
Prints |Y|, |S Y| and sha256 of the uncompressed certificate; exit 0 iff |S Y| < 2|Y|.
"""
import gzip, hashlib, itertools, random, sys
from fractions import Fraction as Fr


def lml(j, w):
    """x_j * (normal form w), as a normal form."""
    out = []
    k = 0
    while k < len(w) and w[k] < j:
        out.append(w[k])
        j += 1
        k += 1
    return tuple(out) + (j,) + tuple(w[k:])


def mul(a, b):
    r = tuple(b)
    for j in reversed(a):
        r = lml(j, r)
    return r


def pl_x(n, t):
    """Piecewise-linear x_n evaluated at a dyadic rational t in [0, 1]."""
    lo = 1 - Fr(1, 2 ** n)
    if t <= lo:
        return t
    s = (t - lo) * 2 ** n  # rescale [lo, 1] to [0, 1]
    if s <= Fr(1, 2):
        u = s / 2
    elif s <= Fr(3, 4):
        u = s - Fr(1, 4)
    else:
        u = 2 * s - 1
    return lo + u / 2 ** n


def pl_word(w, t):
    for j in reversed(w):  # (x_(i_1) ... x_(i_D))(t) = x_(i_1)( ... x_(i_D)(t))
        t = pl_x(j, t)
    return t


def pl_signature(w, depth=7):
    return tuple(pl_word(w, Fr(k, 2 ** depth)) for k in range(2 ** depth + 1))


def selftest():
    grid = [Fr(k, 64) for k in range(65)]
    for i in range(4):
        for j in range(i + 1, 5):
            for t in grid:
                assert pl_word((j, i), t) == pl_word((i, j + 1), t), "PL model violates x_j x_i = x_i x_(j+1)"
    rng = random.Random(11)
    for _ in range(300):
        a = tuple(sorted(rng.randrange(4) for _ in range(rng.randrange(4))))
        b = tuple(sorted(rng.randrange(4) for _ in range(rng.randrange(4))))
        p = mul(a, b)
        assert list(p) == sorted(p)
        for t in grid:
            assert pl_word(p, t) == pl_word(a + b, t), "normal form product disagrees with PL product"
    forms = [w for d in range(4) for w in itertools.combinations_with_replacement(range(4), d)]
    sigs = set(pl_signature(w) for w in forms)
    assert len(sigs) == len(forms), "distinct small normal forms gave equal PL maps"


def parse_monomials(spec):
    return [tuple(int(x) for x in m.split(",")) for m in spec.split(";")]


def check(raw, S, D):
    Y = [tuple(int(x) for x in line.split(",")) for line in raw.decode().splitlines() if line.strip()]
    assert Y, "empty certificate"
    assert len(set(Y)) == len(Y), "duplicate words"
    assert all(len(w) == D and list(w) == sorted(w) for w in Y), "not normal forms of degree D"
    SY = set(mul(s, w) for s in S for w in Y)
    return len(Y), len(SY), hashlib.sha256(raw).hexdigest()


def main():
    selftest()
    path, spec, D = sys.argv[1], sys.argv[2], int(sys.argv[3])
    raw = open(path, "rb").read()
    if path.endswith(".gz"):
        raw = gzip.decompress(raw)
    ny, nsy, h = check(raw, parse_monomials(spec), D)
    ok = nsy < 2 * ny
    print("|Y|", ny, "|SY|", nsy, "witness:", ok, "sha256", h)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
