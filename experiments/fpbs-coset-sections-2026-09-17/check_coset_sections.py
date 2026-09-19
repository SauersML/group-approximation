"""Checks for fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable.

(a) Nonbacktracking polynomial identity A_n = P_n(A_1) on finite Schreier
    graphs of F_2 (random permutation actions), and that the matrix entry
    <delta_0, A_m delta_z> equals #{w in S_m : z.w = 0}, i.e. the number of
    reduced words of length m in the left coset y Stab(0) with y = z^-1.
(b) The Chebyshev bound |P_n(x)| <= (1+1/q)(n+1) max(sqrt q, mu_+(|x|))^n on a
    grid of x in [-(q+1), q+1], q = 2,3,4,6.
(c) Uniform coset sphere counts sup_y #(yJ cap S_m) in F_2 for J = <a> and
    J = <a, b a b^-1>, m <= 11, by exhaustive enumeration of reduced words,
    compared with #(J cap S_m) and with q^m = 3^m.
"""
import itertools
import math
import random

import numpy as np

# ---------------------------------------------------------------- basics
LETTERS = ["a", "A", "b", "B"]  # A = a^-1, B = b^-1
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}


def reduced_words(m):
    if m == 0:
        yield ""
        return
    for w in reduced_words(m - 1):
        for s in LETTERS:
            if w and INV[w[-1]] == s:
                continue
            yield w + s


def P_poly(n, x, q):
    """P_n(x) = q^{n/2}[U_n(t) - U_{n-2}(t)/q], t = x/(2 sqrt q), via the
    recursion P_0=1, P_1=x, P_2=x^2-(q+1), P_{n+1}=x P_n - q P_{n-1}."""
    if n == 0:
        return np.ones_like(x) if isinstance(x, np.ndarray) else 1.0
    p0 = np.eye(x.shape[0]) if isinstance(x, np.ndarray) and x.ndim == 2 else 1.0
    if n == 1:
        return x
    xx = x @ x if isinstance(x, np.ndarray) and x.ndim == 2 else x * x
    p1, p2 = x, xx - (q + 1) * p0
    for _ in range(2, n):
        p1, p2 = p2, (x @ p2 if isinstance(x, np.ndarray) and x.ndim == 2 else x * p2) - q * p1
    return p2


def P_cheb(n, x, q):
    t = x / (2 * math.sqrt(q))
    def U(k):
        if k < 0:
            return 0.0
        if abs(t) < 1:
            th = math.acos(t)
            s = math.sin(th)
            return math.sin((k + 1) * th) / s if abs(s) > 1e-12 else (k + 1) * (1 if t > 0 else (-1) ** k)
        if abs(t) == 1:
            return (k + 1) * (1 if t > 0 else (-1) ** k)
        th = math.acosh(abs(t))
        val = math.sinh((k + 1) * th) / math.sinh(th)
        return val if t > 0 else val * (-1) ** k
    return q ** (n / 2) * (U(n) - U(n - 2) / q)


# ---------------------------------------------------------------- (a)
def part_a(N=40, seed=1, nmax=7):
    rng = random.Random(seed)
    pa = list(range(N)); rng.shuffle(pa)
    pb = list(range(N)); rng.shuffle(pb)
    act = {"a": pa, "b": pb,
           "A": [pa.index(i) for i in range(N)],
           "B": [pb.index(i) for i in range(N)]}
    q = 3
    # right action z.w: apply letters left to right
    def move(z, w):
        for s in w:
            z = act[s][z]
        return z
    A1 = np.zeros((N, N))
    for z in range(N):
        for s in LETTERS:
            A1[z, act[s][z]] += 1
    ok_poly = ok_count = True
    for n in range(0, nmax + 1):
        An = np.zeros((N, N))
        for w in reduced_words(n):
            for z in range(N):
                An[z, move(z, w)] += 1
        Pn = P_poly(n, A1, q) if n > 0 else np.eye(N)
        if not np.allclose(An, Pn):
            ok_poly = False
        # entry <delta_z, A_n delta_0> = #{w in S_n : z.w = 0}
        for z in range(N):
            cnt = sum(1 for w in reduced_words(n) if move(z, w) == 0)
            if cnt != An[z, 0]:
                ok_count = False
        print(f"(a) n={n}: A_n == P_n(A_1): {np.allclose(An, Pn)}; ||A_n|| = {np.linalg.norm(An, 2):.4f}")
    print(f"(a) polynomial identity on all n<={nmax}: {ok_poly}; coset-count entries: {ok_count}")
    # recursion polynomial vs Chebyshev closed form
    ok_cf = all(abs(P_poly(n, x, q) - P_cheb(n, x, q)) < 1e-6 * max(1, abs(P_poly(n, x, q)))
                for n in range(1, 15) for x in np.linspace(-4, 4, 81))
    print(f"(a) recursion P_n equals q^(n/2)[U_n - U_(n-2)/q] on grid, n<15: {ok_cf}")
    return ok_poly and ok_count and ok_cf


# ---------------------------------------------------------------- (b)
def mu_plus(x, q):
    return (x + math.sqrt(x * x - 4 * q)) / 2 if x * x >= 4 * q else 0.0


def part_b():
    ok = True
    worst = 0.0
    for q in (2, 3, 4, 6):
        for n in range(0, 40):
            for x in np.linspace(-(q + 1), q + 1, 801):
                r = max(math.sqrt(q), mu_plus(abs(x), q))
                bound = (1 + 1 / q) * (n + 1) * r ** n
                val = abs(P_poly(n, x, q)) if n > 0 else 1.0
                worst = max(worst, val / bound)
                if val > bound * (1 + 1e-9):
                    ok = False
        print(f"(b) q={q}: mu_+(q+1) = {mu_plus(q + 1, q):.6f} (should be q)")
    print(f"(b) bound holds on grid: {ok}; max ratio |P_n|/bound = {worst:.4f}")
    return ok


# ---------------------------------------------------------------- (c)
def free_reduce(w):
    out = []
    for s in w:
        if out and out[-1] == INV[s]:
            out.pop()
        else:
            out.append(s)
    return "".join(out)


class Stallings:
    """Folded core graph of a finitely generated subgroup of F_2."""
    def __init__(self, gens):
        self.edges = {}  # (v, letter) -> v'
        self.n = 1
        for g in gens:
            v = 0
            for i, s in enumerate(g):
                if i == len(g) - 1:
                    tgt = 0
                else:
                    tgt = self.n; self.n += 1
                self._add(v, s, tgt)
                v = tgt
        self._fold()

    def _add(self, v, s, u):
        self.edges.setdefault((v, s), set()).add(u)
        self.edges.setdefault((u, INV[s]), set()).add(v)

    def _fold(self):
        changed = True
        while changed:
            changed = False
            for (v, s), tg in list(self.edges.items()):
                if len(tg) > 1:
                    keep, *rest = sorted(tg)
                    for r in rest:
                        self._merge(keep, r)
                    changed = True
                    break

    def _merge(self, u, r):
        new = {}
        for (v, s), tg in self.edges.items():
            v2 = u if v == r else v
            for t in tg:
                t2 = u if t == r else t
                new.setdefault((v2, s), set()).add(t2)
        self.edges = new

    def coset(self, x):
        """Normal form of the right coset J x, x reduced: (core vertex, suffix)."""
        v = 0
        for i, s in enumerate(x):
            tg = self.edges.get((v, s))
            if not tg:
                return (v, x[i:])
            v = next(iter(tg))
        return (v, "")


def inverse(w):
    return "".join(INV[s] for s in reversed(w))


def part_c(mmax=11):
    subgroups = {"<a>": ["a"], "<a, b a b^-1>": ["a", "baB"]}
    q = 3
    res = {}
    for name, gens in subgroups.items():
        st = Stallings(gens)
        print(f"(c) J = {name}: core has {len(set(v for v, _ in st.edges))} vertices")
        rows = []
        for m in range(1, mmax + 1):
            counts = {}
            inJ = 0
            for w in reduced_words(m):
                # w lies in the left coset yJ  iff  J w^-1 = J y^-1
                key = st.coset(inverse(w))
                counts[key] = counts.get(key, 0) + 1
                if key == (0, ""):
                    inJ += 1
            sup = max(counts.values())
            rows.append((m, inJ, sup))
            print(f"    m={m:2d}  #(J cap S_m)={inJ:6d}  sup_y #(yJ cap S_m)={sup:6d}  "
                  f"sup^(1/m)={sup ** (1 / m):.4f}  q^m={q ** m}")
        res[name] = rows
    return res


if __name__ == "__main__":
    a = part_a()
    b = part_b()
    c = part_c()
    print("ALL IDENTITY/BOUND CHECKS PASS:", a and b)
