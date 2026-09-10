#!/usr/bin/env python3
"""sp-design for the lead: c_2 DIRECTLY, and hence kappa(1,1) = c_2 / c_1^2.

Rather than compute the Cartan comparison's coefficient at the top splitting (which needs
the riffle sign and the evaluation reordering as well as the coproduct), build the
equivariant diagonal Phi itself on the MODELS and read both constants off.  That settles
the same question with strictly less sign bookkeeping, and it produces c_1 independently
of the Delta^1 cochain descent, which is a real cross-check on that number too.

CONSTRUCTION.  Phi : W (x) C_*(X) -> C_*(X)^{(x)p}, natural, equivariant, with
Phi(e_0 (x) -) the iterated Alexander-Whitney diagonal.  On the models it is determined by
the chain-map condition
    d Phi(e_a (x) iota_n) = alpha_a . Phi(e_{a-1} (x) iota_n)
                          + (-1)^a sum_j (-1)^j (face_j)_# Phi(e_a (x) iota_{n-1}),
alpha_a = s = T - 1 for a odd, N for a even, and it is solved by the cone contraction:
C_*(Delta^n) has s(sigma) = [0, sigma] (0 if 0 in sigma) with d s + s d = 1 - eta eps, so
S := s (x) 1 (x) ... (x) 1 satisfies d S + S d = 1 - (eta eps)(x)1 on the p-fold power.

READING OFF THE CONSTANTS.  Phi(e_a (x) iota_n) has degree n + a.  At a = n(p-1) that is
n p, the TOP degree of C_*(Delta^n)^{(x)p}, whose only basis element is [0..n]^{(x)p}.  So
    Phi(e_{n(p-1)} (x) iota_n) = lambda_n . [0..n]^{(x)p}
and, for a degree-n cocycle w on a space X and a singular n-chain sigma,
    < D_{n(p-1)}(w), sigma > = < w^{(x)p}, Phi(e_{n(p-1)} (x) sigma) >
                             = lambda_n . (Koszul) . <w, sigma>^p .
On the minimal torus (1 vertex, 3 edges a,b,c, 2 triangles U,L with the fundamental cycle
U - L) the degree-2 class w = u cup v has <w,U> = 1 and <w,L> = 0, so
<D(w), U-L> = lambda_2 . (Koszul) and <w, U-L> = 1, giving c_2 = +- lambda_2.  Likewise
c_1 = +- lambda_1 from Delta^1.  Both signs are conventions; only the ratio matters, and
kappa(1,1) = c_2 / c_1^2.
"""
import sys
from itertools import combinations, product


# ------------------------------------------------------------------ faces of Delta^n

def faces(n):
    out = []
    for k in range(1, n + 2):
        out.extend(combinations(range(n + 1), k))
    return out


def deg(f):
    return len(f) - 1


def boundary(f):
    """d[i_0..i_k] = sum_j (-1)^j [.. hat i_j ..]"""
    if len(f) == 1:
        return {}
    out = {}
    for j in range(len(f)):
        g = f[:j] + f[j + 1:]
        out[g] = out.get(g, 0) + (-1) ** j
    return {k: v for k, v in out.items() if v}


def cone(f):
    """s(sigma) = [0, sigma] if 0 not in sigma, else 0."""
    if f[0] == 0:
        return None
    return (0,) + f


# ------------------------------------------------------------------ tensor power ops

def wdeg(w):
    return sum(deg(f) for f in w)


def Dtot(vec, p):
    out = {}
    for w, c in vec.items():
        if not c % p:
            continue
        pre = 0
        for l, f in enumerate(w):
            for g, cg in boundary(f).items():
                w2 = w[:l] + (g,) + w[l + 1:]
                out[w2] = (out.get(w2, 0) + ((-1) ** pre) * cg * c) % p
            pre += deg(f)
    return {k: v for k, v in out.items() if v % p}


def Stot(vec, p):
    """the FULL tensor-product contraction
       S = sum_l (eta eps)^{(x)(l-1)} (x) s (x) 1 (x) ... (x) 1 ,
    which satisfies D S + S D = 1 - (eta eps)^{(x)p}.  No Koszul signs appear: the l-th
    term is nonzero only when slots 1..l-1 are vertices, i.e. have degree 0."""
    out = {}
    for w, c in vec.items():
        for l in range(len(w)):
            if any(deg(f) != 0 for f in w[:l]):
                break
            g = cone(w[l])
            if g is None:
                continue
            w2 = ((0,),) * l + (g,) + w[l + 1:]
            out[w2] = (out.get(w2, 0) + c) % p
    return {k: v for k, v in out.items() if v % p}


def Ttot(vec, p):
    """move the LAST factor to the front, with the Koszul sign."""
    out = {}
    for w, c in vec.items():
        dl = deg(w[-1])
        s = (-1) ** (dl * (wdeg(w) - dl))
        w2 = (w[-1],) + w[:-1]
        out[w2] = (out.get(w2, 0) + s * c) % p
    return {k: v for k, v in out.items() if v % p}


def Ntot(vec, p):
    out = {}
    cur = dict(vec)
    for _ in range(p):
        for k, v in cur.items():
            out[k] = (out.get(k, 0) + v) % p
        cur = Ttot(cur, p)
    return {k: v for k, v in out.items() if v % p}


def SminusOne(vec, p):
    out = dict(Ttot(vec, p))
    for k, v in vec.items():
        out[k] = (out.get(k, 0) - v) % p
    return {k: v for k, v in out.items() if v % p}


def addv(a, b, p, s=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = (out.get(k, 0) + s * v) % p
    return {k: v for k, v in out.items() if v % p}


def facemap(vec, j, n, p):
    """(delta_j)_# : C_*(Delta^{n-1}) -> C_*(Delta^n), the j-th face inclusion."""
    def img(f):
        return tuple(x if x < j else x + 1 for x in f)
    out = {}
    for w, c in vec.items():
        w2 = tuple(img(f) for f in w)
        out[w2] = (out.get(w2, 0) + c) % p
    return {k: v for k, v in out.items() if v % p}


def aw(n, p):
    """iterated AW diagonal of [0..n]."""
    out = {}
    for cuts in product(range(n + 1), repeat=p - 1):
        if any(cuts[i] > cuts[i + 1] for i in range(len(cuts) - 1)):
            continue
        idx = (0,) + cuts + (n,)
        w = tuple(tuple(range(idx[j], idx[j + 1] + 1)) for j in range(p))
        out[w] = (out.get(w, 0) + 1) % p
    return {k: v for k, v in out.items() if v % p}


# ------------------------------------------------------------------ build Phi

def build_phi(p, nmax, amax, verbose=False):
    """phi[n][a] = Phi(e_a (x) iota_n)."""
    phi = {}
    for n in range(0, nmax + 1):
        phi[n] = {0: aw(n, p)}
        for a in range(1, amax + 1):
            rhs = {}
            prev = phi[n].get(a - 1, {})
            if prev:
                rhs = addv(rhs, Ntot(prev, p) if a % 2 == 0 else SminusOne(prev, p), p)
            if n >= 1:
                sub = phi[n - 1].get(a, {})
                if sub:
                    acc = {}
                    for j in range(n + 1):
                        acc = addv(acc, facemap(sub, j, n, p), p, (-1) ** j)
                    rhs = addv(rhs, acc, p, (-1) ** a)
            if not rhs:
                phi[n][a] = {}
                continue
            assert not Dtot(rhs, p), f"rhs is not a cycle at n={n}, a={a}"
            X = Stot(rhs, p)
            assert not addv(Dtot(X, p), rhs, p, -1), (
                f"chain map fails at n={n}, a={a}", list(
                    addv(Dtot(X, p), rhs, p, -1).items())[:3])
            phi[n][a] = X
        if verbose:
            print(f"   n={n}: supports " +
                  str([len(phi[n].get(a, {})) for a in range(0, amax + 1)]), flush=True)
    return phi


def top_coeff(vec, n, p):
    top = (tuple(range(n + 1)),) * p
    return vec.get(top, 0) % p


def sym(c, p):
    return c if c <= p // 2 else c - p


if __name__ == "__main__":
    primes = [3, 5, 7]
    if len(sys.argv) > 1:
        primes = [int(a) for a in sys.argv[1:]]
    for p in primes:
        print("=" * 66, flush=True)
        amax = 2 * (p - 1)
        try:
            phi = build_phi(p, 2, amax, verbose=True)
        except AssertionError as e:
            print(f"p = {p}: {e}", flush=True)
            continue
        lam1 = top_coeff(phi[1].get(p - 1, {}), 1, p)
        lam2 = top_coeff(phi[2].get(2 * (p - 1), {}), 2, p)
        import math
        m = math.factorial((p - 1) // 2) % p
        inv = pow(lam1, p - 2, p) if lam1 % p else None
        kap = (lam2 * pow(lam1 * lam1 % p, p - 2, p)) % p if lam1 % p else None
        print(f"p = {p}:  c_1 = lambda_1 = {sym(lam1,p)}   ((p-1)/2)! = {sym(m,p)}   "
              f"match: {lam1 % p == m}", flush=True)
        print(f"         c_2 = lambda_2 = {sym(lam2,p)}   c_1^2 = {sym(lam1*lam1 % p, p)}",
              flush=True)
        print(f"         kappa(1,1) = c_2 / c_1^2 = "
              f"{sym(kap,p) if kap is not None else 'undefined'}   "
              f"({'NONZERO' if lam2 % p else 'ZERO'} c_2)", flush=True)
