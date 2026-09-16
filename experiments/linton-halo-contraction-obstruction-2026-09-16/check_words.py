#!/usr/bin/env python3
"""Exact word-level checks for the contraction obstruction to Linton halos.

Checks (all exact, no floating point):
  1. The relator of G0 = <a,s | s a s^-1 = [a, s^-1 a s]> is cyclically reduced
     of length 11, has s-exponent 0 and a-exponent 1.
  2. Tietze: substituting a_{-1} = s^-1 a s, a_0 = a turns the ascending-HNN
     relations s a_{-1} s^-1 = a_0, s a_0 s^-1 = [a_0, a_{-1}] into free
     identities plus the relator of G0.
  3. phi: x -> y, y -> [y,x] on F(x,y) has image <y, x y x^-1> (Nielsen reduced
     generating set of rank 2), so phi is injective; x is not in the image
     (the image lies in the normal closure of y).
  4. The abelianization of the ascending HNN extension F(x,y) *_{phi^N} is Z
     for N = 1..6 (Smith normal form of the relation matrix).
  5. For u = [p,q], the Fox derivatives of u^k (k = 1..6) do not vanish in
     Z[Z^2], so u^k is not in F(p,q)''.
Conventions: [g,h] = g h g^-1 h^-1.  Letters are (name, +-1).
"""
from fractions import Fraction
from itertools import product


def inv(w):
    return [(g, -e) for (g, e) in reversed(w)]


def red(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]:
            out.pop()
        else:
            out.append(x)
    return out


def mul(*ws):
    r = []
    for w in ws:
        r = red(r + list(w))
    return r


def comm(g, h):
    return mul(g, h, inv(g), inv(h))


def gen(name):
    return [(name, 1)]


def cyc_reduced(w):
    return len(w) > 0 and not (w[0][0] == w[-1][0] and w[0][1] == -w[-1][1])


def expsum(w, name):
    return sum(e for (g, e) in w if g == name)


def subst(w, images):
    r = []
    for (g, e) in w:
        img = images[g]
        r = mul(r, img if e == 1 else inv(img))
    return r


def fmt(w):
    return " ".join(g + ("" if e == 1 else "^-1") for (g, e) in w) or "1"


ok = True


def check(cond, msg):
    global ok
    print(("PASS " if cond else "FAIL ") + msg)
    ok = ok and cond


a, s = gen("a"), gen("s")
# 1. relator of G0
rel = mul(s, a, inv(s), inv(comm(a, mul(inv(s), a, s))))
print("relator w =", fmt(rel))
check(len(rel) == 11 and cyc_reduced(rel), "relator cyclically reduced of length 11")
check(expsum(rel, "s") == 0 and expsum(rel, "a") == 1, "exponent sums s:0, a:1")

# 2. Tietze from the ascending HNN presentation
am1, a0 = mul(inv(s), a, s), a
r1 = mul(s, am1, inv(s), inv(a0))            # s a_{-1} s^-1 a_0^-1
r2 = mul(s, a0, inv(s), inv(comm(a0, am1)))   # s a_0 s^-1 [a_0,a_{-1}]^-1
check(r1 == [], "first HNN relation becomes a free identity")
check(r2 == rel, "second HNN relation becomes the relator of G0")

# 3. phi and Nielsen reduction of {y, x y x^-1}
x, y = gen("x"), gen("y")
phi = {"x": y, "y": comm(y, x)}
img = [subst(x, phi), subst(y, phi)]
print("phi(x) =", fmt(img[0]), "; phi(y) =", fmt(img[1]))
# <y, [y,x]> = <y, x y x^-1>: [y,x] = y (x y^-1 x^-1), so x y x^-1 = ([y,x]^-1 y)
check(mul(inv(img[1]), y) == mul(x, y, inv(x)), "[y,x]^-1 y = x y x^-1")
basis = [y, mul(x, y, inv(x))]
elts = basis + [inv(b) for b in basis]


def is_inv_pair(u, v):
    return mul(u, v) == []


n1 = all(len(u) > 0 for u in basis)
n2 = all(len(mul(u, v)) >= max(len(u), len(v))
         for u, v in product(elts, repeat=2) if not is_inv_pair(u, v))
n3 = all(len(mul(u, v, w)) > len(u) - len(v) + len(w)
         for u, v, w in product(elts, repeat=3)
         if not is_inv_pair(u, v) and not is_inv_pair(v, w))
check(n1 and n2 and n3, "{y, x y x^-1} is Nielsen reduced (rank-2 free basis)")
# image in normal closure of y: kill y
killy = {"x": x, "y": []}
check(subst(img[0], killy) == [] and subst(img[1], killy) == [],
      "image of phi dies when y is killed, so x is not in the image")


# 4. abelianization of F(x,y) *_{phi^N}
def ab(w, names):
    return [expsum(w, n) for n in names]


def smith_invariants(M):
    """Return nonzero diagonal of Smith normal form of an integer matrix."""
    A = [row[:] for row in M]
    rows, cols = len(A), len(A[0])
    diag = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        # find pivot with minimal abs value in submatrix column c
        while True:
            piv = None
            for i in range(r, rows):
                for j in range(c, cols):
                    if A[i][j] != 0 and (piv is None or abs(A[i][j]) < abs(A[piv[0]][piv[1]])):
                        piv = (i, j)
            if piv is None:
                return diag
            i, j = piv
            A[r], A[i] = A[i], A[r]
            for row in A:
                row[c], row[j] = row[j], row[c]
            done = True
            for i in range(r + 1, rows):
                q = A[i][c] // A[r][c]
                A[i] = [A[i][k] - q * A[r][k] for k in range(cols)]
                if A[i][c] != 0:
                    done = False
            for j in range(c + 1, cols):
                q = A[r][j] // A[r][c]
                for i in range(rows):
                    A[i][j] -= q * A[i][c]
                if A[r][j] != 0:
                    done = False
            if done:
                break
        diag.append(abs(A[r][c]))
        r += 1
    return diag


phiN = {"x": x, "y": y}
for N in range(1, 7):
    phiN = {g: subst(phiN[g], phi) for g in ("x", "y")}
    names = ["x", "y", "t"]
    M = []
    for g in ("x", "y"):
        v = ab(gen(g), names)
        wv = ab(phiN[g], names)
        M.append([v[i] - wv[i] for i in range(3)])
    d = smith_invariants(M)
    rank_free = 3 - len(d)
    tors = [q for q in d if q != 1]
    check(rank_free == 1 and not tors, f"H1 of F(x,y) *_(phi^{N}) is Z (relation matrix {M})")


# 5. Fox derivatives of u^k in Z[Z^2], u = [p,q]
def fox(w, g):
    """Fox derivative d w / d g, mapped to Z[Z^2] = Laurent polys in (P,Q).
    Represented as dict {(i,j): coeff}.  Prefix of w maps to (exp_p, exp_q)."""
    res = {}
    ip = iq = 0
    for (h, e) in w:
        if h == g:
            if e == 1:
                key = (ip, iq)
                res[key] = res.get(key, 0) + 1
            else:
                key = (ip - (1 if h == "p" else 0), iq - (1 if h == "q" else 0))
                res[key] = res.get(key, 0) - 1
        if h == "p":
            ip += e
        else:
            iq += e
    return {k: v for k, v in res.items() if v != 0}


p, q = gen("p"), gen("q")
u = comm(p, q)
for k in range(1, 7):
    uk = mul(*([u] * k))
    dp, dq = fox(uk, "p"), fox(uk, "q")
    check(bool(dp) and bool(dq), f"Fox derivatives of u^{k} nonzero: d/dp = {sorted(dp.items())}")
# conjugates: the Fox derivative of g u^k g^-1 is translated/nonzero as well
g = mul(p, q, p)
guk = mul(g, u, u, inv(g))
check(bool(fox(guk, "p")) or bool(fox(guk, "q")), "a conjugate of u^2 is not in F''")

print("ALL PASS" if ok else "SOME FAIL")
