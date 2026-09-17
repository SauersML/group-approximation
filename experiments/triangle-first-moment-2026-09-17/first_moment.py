"""Independent-conjugation first moment for homomorphisms of a triangle of
finite groups (trivial face group, cyclic edge groups of prime order) into S_n.

Input per vertex group H with its two edge generators g1, g2: one line per
conjugacy class of subgroups U, "index classlength c1 c2", where c_i is the
number of p_i-cycles of g_i on H/U (produced by subgroup_data.g).

H_v(n; c1, c2) = number of homomorphisms H -> S_n in which g_i has c_i cycles
of length p_i, computed exactly from the marked exponential formula
    sum_n H_v(n; .) x^n/n! = exp( sum_U x^[H:U] y1^c1(U) y2^c2(U) / [H:U] ).

For a tree (a path v1 - v2 - v3 amalgam) the count of homomorphisms is exact:
    T(n) = sum H1(c12,c13) H2(c12,*) H3(c13,*) / (K(c12) K(c13)),
because conjugation acts transitively on each cycle class.  For the triangle
the third edge identification is modelled as an independent event of
probability 1/K(c23):
    E(n) = sum H1(c12,c13) H2(c12,c23) H3(c13,c23) / (K(c12) K(c13) K(c23)).
K_p(c) = n! / (p^c c! (n - p c)!) is the size of the S_n-class with c p-cycles.
The c = 0 term is the trivial homomorphism when the vertex groups are simple.
"""
import sys
from fractions import Fraction
from math import factorial, log10


def load(path):
    rows = []
    for line in open(path):
        k, ln, c1, c2 = map(int, line.split())
        rows.append((k, ln, c1, c2))
    return rows


def marked_hom_counts(rows, N):
    s = {}
    for k, ln, c1, c2 in rows:
        d = s.setdefault(k, {})
        d[(c1, c2)] = d.get((c1, c2), 0) + ln
    h = [{(0, 0): 1}]
    for n in range(1, N + 1):
        acc = {}
        for k, sk in s.items():
            if k > n:
                continue
            f = factorial(n - 1) // factorial(n - k)
            for (a1, a2), va in sk.items():
                for (b1, b2), vb in h[n - k].items():
                    key = (a1 + b1, a2 + b2)
                    acc[key] = acc.get(key, 0) + f * va * vb
        h.append(acc)
    return h


def K(n, p, c):
    return factorial(n) // (p ** c * factorial(c) * factorial(n - p * c))


def margin(hv, which):
    out = {}
    for (c1, c2), v in hv.items():
        key = c1 if which == 1 else c2
        out[key] = out.get(key, 0) + v
    return out


def triangle_moment(h1, h2, h3, p12, p13, p23, n):
    """v1 has edges (e12, e13), v2 has (e12, e23), v3 has (e13, e23)."""
    E = Fraction(0)
    for (c12, c13), a in h1[n].items():
        for (d12, c23), b in h2[n].items():
            if d12 != c12:
                continue
            c = h3[n].get((c13, c23), 0)
            if c:
                E += Fraction(a * b * c, K(n, p12, c12) * K(n, p13, c13) * K(n, p23, c23))
    return E


def tree_count(h1, h2, h3, p12, p13, n):
    m2 = margin(h2[n], 1)
    m3 = margin(h3[n], 1)
    T = Fraction(0)
    for (c12, c13), a in h1[n].items():
        b = m2.get(c12, 0)
        c = m3.get(c13, 0)
        if b and c:
            T += Fraction(a * b * c, K(n, p12, c12) * K(n, p13, c13))
    return T


def lg(x):
    x = Fraction(x)
    if x <= 0:
        return float("-inf")
    return log10(x.numerator) - log10(x.denominator)


if __name__ == "__main__":
    mode = sys.argv[1]
    N = int(sys.argv[2])
    if mode == "a7a7a8":
        a7 = marked_hom_counts(load("A7.dat"), N)
        a8 = marked_hom_counts(load("A8.dat"), N)
        tri = (a7, a7, a8, 7, 7, 7)
    elif mode.startswith("coxeter"):
        ms = list(map(int, mode.split(":")[1].split(",")))  # m_ab, m_bc, m_ca
        hs = [marked_hom_counts(load("D%d.dat" % m), N) for m in ms]
        # v1 = D(m_ab) on (a, b); v2 = D(m_bc) on (b, c); v3 = D(m_ca) on (c, a).
        # Triangle edges: e12 = b, e13 = a, e23 = c.  Reorder the markings.
        def swap(h):
            return [{(c2, c1): v for (c1, c2), v in hn.items()} for hn in h]
        tri = (swap(hs[0]), hs[1], swap(hs[2]), 2, 2, 2)
    else:
        raise SystemExit("mode")
    print("n  log10(E(n)-1)  log10(T(n)-1)")
    for n in range(1, N + 1):
        E = triangle_moment(*tri, n)
        T = tree_count(tri[0], tri[1], tri[2], tri[3], tri[4], n)
        print(n, "%.3f" % lg(E - 1), "%.3f" % lg(T - 1), flush=True)
