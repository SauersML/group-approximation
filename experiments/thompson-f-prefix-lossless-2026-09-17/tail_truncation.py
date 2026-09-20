#!/usr/bin/env python3
"""Checks for thompson-f-prefix-observation-is-lossless.

Forests of the positive monoid M of Thompson's F: a finite tuple of binary trees
(None = trivial tree), followed implicitly by infinitely many trivial trees.
Left multiplication by x_k merges roots k and k+1.  For a normal form
s = x_(i_1) ... x_(i_d), s.y = x_(i_1)(x_(i_2)(... x_(i_d) y)).

Checked exhaustively on small forests:
  (R)  x_j x_i = x_i x_(j+1) for i < j (convention check);
  (Guba sets named S_(m+1,m+d+1) as in the graph; J = m is asserted.)
  (A)  z in sM  <=>  tau_J z in sM;
  (B)  split_s(tau_J z) = tau_(J+d)(split_s z);
where J = J(S) is the largest root index of z touched by any s in S (J <= I),
and tau_J trivialises every tree at a position > J.
  (C)  the identity D^Psi(mu', eta') = D^(Psi o tau)(mu, eta) of the node, for random
       finitely supported mu, eta and several observations Psi, in exact rationals.
Run:  python3 tail_truncation.py      (about ten seconds)
"""
import itertools, random
from fractions import Fraction

def norm(f):
    f = list(f)
    while f and f[-1] is None:
        f.pop()
    return tuple(f)

def get(f, q):
    return f[q] if q < len(f) else None

def merge(k, y):
    y = list(y) + [None] * max(0, k + 2 - len(y))
    return norm(y[:k] + [(y[k], y[k + 1])] + y[k + 2:])

def act(word, y):
    for k in reversed(word):
        y = merge(k, y)
    return y

def split(word, z):
    """y with act(word, y) = z, or None if z is not in word.M."""
    y = z
    for k in word:
        t = get(y, k)
        if t is None:
            return None
        y = list(y) + [None] * max(0, k + 1 - len(y))
        y = norm(y[:k] + [t[0], t[1]] + y[k + 1:])
    return y

def tau(J, f):
    return norm(f[:J + 1])

def trees(n):
    """All binary trees with exactly n carets."""
    if n == 0:
        return [None]
    out = []
    for a in range(n):
        for L in trees(a):
            for R in trees(n - 1 - a):
                out.append((L, R))
    return out

def forests(width, carets):
    """All forests supported on the first `width` roots with <= carets carets."""
    out = set()
    for comp in itertools.product(range(carets + 1), repeat=width):
        if sum(comp) > carets:
            continue
        for ts in itertools.product(*[trees(c) for c in comp]):
            out.add(norm(ts))
    return sorted(out, key=repr)

def guba(m, d):
    """S_(m+1,m+d+1): normal forms i_1 <= ... <= i_d with i_j <= m+j-1."""
    out = []
    def rec(prefix):
        j = len(prefix)
        if j == d:
            out.append(tuple(prefix)); return
        lo = prefix[-1] if prefix else 0
        for i in range(lo, m + j + 1):
            rec(prefix + [i])
    rec([])
    return out

def touched(word):
    """Largest root index of s.y that contains a caret of s."""
    marker = tuple(('leaf', q) for q in range(40))
    z = act(word, marker)
    return max(q for q in range(len(z)) if z[q][0] != 'leaf')

def depth(t):
    return -1 if t is None else 1 + max(depth(t[0]), depth(t[1]))

def D(S, Psi, mu, eta, lam):
    tot = Fraction(0)
    for s in S:
        P = {}
        for y, p in mu.items():
            P[Psi(y)] = P.get(Psi(y), 0) + p
        for z, p in eta.items():
            y = split(s, z)
            if y is not None:
                P[Psi(y)] = P.get(Psi(y), 0) - lam * p
        tot += sum(v for v in P.values() if v > 0)
    return tot

def push(f, law):
    out = {}
    for x, p in law.items():
        out[f(x)] = out.get(f(x), 0) + p
    return out

def main():
    # (R)
    for i in range(4):
        for j in range(i + 1, 5):
            for y in forests(7, 3)[:400]:
                assert act((j, i), y) == act((i, j + 1), y)
    print("(R) x_j x_i = x_i x_(j+1): ok")
    rng = random.Random(20260917)
    sets = {"S_(2,3)": guba(1, 1), "S_(2,4)": guba(1, 2), "S_(3,5)": guba(2, 2), "S_(2,5)": guba(1, 3)}
    for name in ["rand_a", "rand_b", "rand_c"]:
        d = rng.randint(1, 3)
        S = set()
        while len(S) < 5:
            S.add(tuple(sorted(rng.randint(0, 4) for _ in range(d))))
        sets[name] = sorted(S)
    universe = forests(7, 5)
    for name, S in sets.items():
        I = max(max(s) for s in S)
        d = len(S[0]); assert all(len(s) == d for s in S)
        J = max(touched(s) for s in S)
        assert J <= I
        if name.startswith('S_('):
            assert J == int(name[3]) - 1
        n_in = 0
        for s in S:
            for z in universe:
                y = split(s, z)
                assert (y is None) == (split(s, tau(J, z)) is None)        # (A)
                if y is not None:
                    n_in += 1
                    assert act(s, y) == z
                    assert split(s, tau(J, z)) == tau(J + d, y)            # (B)
        print(f"(A),(B) {name}: |S|={len(S)} d={d} I={I} J={J} K={I+d+1} "
              f"forests={len(universe)} splits={n_in}: ok")
    # (C)
    for name in ["S_(2,3)", "S_(2,4)", "S_(3,5)", "rand_a"]:
        S = sets[name]; d = len(S[0]); J = max(touched(s) for s in S)
        K = J + d + 1
        obs = {"id": lambda y: y,
               "depths+exact tail": lambda y, K=K: (tuple(depth(get(y, q)) for q in range(K)), y[K:]),
               "N_y+prefix sizes": lambda y, K=K: (len(y), tuple(repr(get(y, q)).count('(') for q in range(K)))}
        for trial in range(20):
            supp = rng.sample(universe, 30)
            mu = {y: Fraction(rng.randint(1, 9)) for y in supp[:15]}
            eta = {z: Fraction(rng.randint(1, 9)) for z in supp[15:]}
            for law in (mu, eta):
                t = sum(law.values())
                for k in law:
                    law[k] /= t
            mu2 = push(lambda y: tau(J + d, y), mu)
            eta2 = push(lambda z: tau(J, z), eta)
            for oname, Psi in obs.items():
                for lam in (Fraction(1), Fraction(3, 2)):
                    lhs = D(S, Psi, mu2, eta2, lam)
                    rhs = D(S, lambda y: Psi(tau(J + d, y)), mu, eta, lam)
                    assert lhs == rhs, (name, oname, lhs, rhs)
        print(f"(C) {name}: D^Psi(mu',eta') = D^(Psi o tau_(J+d))(mu,eta) on 20 random pairs, 3 observations, lambda in {{1, 3/2}}: ok")

if __name__ == "__main__":
    main()
