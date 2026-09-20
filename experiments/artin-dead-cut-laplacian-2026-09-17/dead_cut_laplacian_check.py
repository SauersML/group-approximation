"""Checks for artin-sigma1-equals-dead-cut-laplacian-surjectivity.

(1) Symbolic, in the free group ring Z F(u, v): the Fox rows of the Artin relator
    r = prod(u,v,l) prod(v,u,l)^{-1} satisfy, modulo r = 1,
      even l = 2k:  d r/du = (1 - v) S_k(uv),   d r/dv = (u - 1) S_k(vu);
      odd  l = 2k+1: d r/du = sum_{j<=k} (uv)^j - sum_{j<k} (vu)^j v.
    Checked for 2 <= l <= 14 (exact word arithmetic, the relation r = 1 is used only
    in the form "every word w r w' equals w w'", which we implement by comparing
    d r/du with the free-group-ring expression D(W1) - r D(W2)).
(2) Levels: for a character with chi(u), chi(v) as in each case, every nonzero
    level of the living-edge factor carries exactly one word, with coefficient +-1.
    So its lowest-level part is +-(one group element): a Novikov unit.
(3) End-to-end numerical check of the reduction theorem.  For random labelled graphs,
    random integer characters (constant along odd edges, with dead vertices allowed
    when dominant) and random matrix representations
        g -> t^chi(g) lambda(g) rho(g),
    rho a Coxeter-type reflection representation of W(m') with m'_e | l_e, lambda a
    random scalar character, t a random complex number, compare
      dim H_1 of the full twisted presentation complex
    with
      dim coker of the dead-cut Laplacian L : (+)_relations F^n -> K_r.
    The theorem's derivation uses only invertibility of the listed "living" factors,
    so it holds over any coefficient ring where they are invertible; the script
    checks those determinants are nonzero, then checks equality of dimensions.
"""
import itertools
import math
import random

import numpy as np

# ---------------------------------------------------------------- free group ring
def red(word):
    out = []
    for a in word:
        if out and out[-1][0] == a[0] and out[-1][1] == -a[1]:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def inv(word):
    return tuple((x, -e) for (x, e) in reversed(word))


def mul(p, q):
    r = {}
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = red(w1 + w2)
            r[w] = r.get(w, 0) + c1 * c2
    return {w: c for w, c in r.items() if c}


def add(*ps):
    r = {}
    for p in ps:
        for w, c in p.items():
            r[w] = r.get(w, 0) + c
    return {w: c for w, c in r.items() if c}


def scal(c, p):
    return {w: c * x for w, x in p.items() if c * x}


def el(word):
    return {red(word): 1}


ONE = {(): 1}


def fox(word, x):
    """Fox derivative d(word)/dx in Z F."""
    r = {}
    for i, (y, e) in enumerate(word):
        if y != x:
            continue
        if e == 1:
            pre = red(word[:i])
            r[pre] = r.get(pre, 0) + 1
        else:
            pre = red(word[: i + 1])
            r[pre] = r.get(pre, 0) - 1
    return {w: c for w, c in r.items() if c}


def prod_word(u, v, l):
    return tuple(((u, 1) if i % 2 == 0 else (v, 1)) for i in range(l))


def relator(u, v, l):
    return red(prod_word(u, v, l) + inv(prod_word(v, u, l)))


def S(k, word):
    r = {}
    for j in range(k):
        r = add(r, el(word * j))
    return r


def check_fox_formulas(maxl=14):
    u, v = "u", "v"
    ok = True
    for l in range(2, maxl + 1):
        W1, W2 = prod_word(u, v, l), prod_word(v, u, l)
        r = relator(u, v, l)
        # d(W1 W2^-1)/dx = dW1/dx - W1 W2^-1 dW2/dx  (exact in Z F)
        for x in (u, v):
            lhs = fox(r, x)
            rhs = add(fox(W1, x), scal(-1, mul(el(r), fox(W2, x))))
            ok &= lhs == rhs
        # modulo r = 1 the derivative is dW1/dx - dW2/dx; compare with closed forms
        du = add(fox(W1, u), scal(-1, fox(W2, u)))
        dv = add(fox(W1, v), scal(-1, fox(W2, v)))
        uv, vu = ((u, 1), (v, 1)), ((v, 1), (u, 1))
        if l % 2 == 0:
            k = l // 2
            ok &= du == mul(add(ONE, scal(-1, el(((v, 1),)))), S(k, uv))
            ok &= dv == mul(add(el(((u, 1),)), scal(-1, ONE)), S(k, vu))
        else:
            k = (l - 1) // 2
            want = add(S(k + 1, uv), scal(-1, mul(S(k, vu), el(((v, 1),)))))
            ok &= du == want
        # fundamental formula: du (u - 1) + dv (v - 1) = W1 - W2 (= 0 in G)
        f = add(mul(du, add(el(((u, 1),)), scal(-1, ONE))),
                mul(dv, add(el(((v, 1),)), scal(-1, ONE))))
        ok &= f == add(el(W1), scal(-1, el(W2)))
    return ok


def check_levels(maxl=14):
    """Living-edge factors: each chi-level carries one word with coefficient +-1."""
    u, v = "u", "v"
    ok = True
    for l in range(2, maxl + 1):
        W1, W2 = prod_word(u, v, l), prod_word(v, u, l)
        du = add(fox(W1, u), scal(-1, fox(W2, u)))
        if l % 2 == 0:
            k = l // 2
            polys = [(S(k, ((u, 1), (v, 1))), cu, cv)
                     for cu in range(-3, 4) for cv in range(-3, 4)
                     if cu and cv and cu + cv != 0]
        else:
            polys = [(du, c, c) for c in range(-3, 4) if c]
        for p, cu, cv in polys:
            lev = {}
            for w, c in p.items():
                h = sum((cu if x == u else cv) * e for x, e in w)
                lev.setdefault(h, []).append(c)
            ok &= all(len(cs) == 1 and abs(cs[0]) == 1 for cs in lev.values())
    return ok


# ---------------------------------------------------------------- numerics
def coxeter_rep(V, mprime, rng):
    """Reflection representation of the Coxeter group W(m'): s -> I - 2 e_s B."""
    n = len(V)
    idx = {x: i for i, x in enumerate(V)}
    B = np.eye(n)
    for (a, b), m in mprime.items():
        val = -1.0 if m is None else -math.cos(math.pi / m)
        B[idx[a], idx[b]] = B[idx[b], idx[a]] = val
    for (a, b) in itertools.combinations(V, 2):
        if (a, b) not in mprime and (b, a) not in mprime:
            B[idx[a], idx[b]] = B[idx[b], idx[a]] = -1.0 - rng.random()
    mats = {}
    for x in V:
        M = np.eye(n)
        M[:, idx[x]] -= 2 * B[:, idx[x]]  # reflection in the column convention
        mats[x] = M
    return mats


class Rep:
    def __init__(self, gens, chi, t):
        self.g, self.chi, self.t = gens, chi, t
        self.n = next(iter(gens.values())).shape[0]

    def word(self, w):
        M = np.eye(self.n, dtype=complex)
        for x, e in w:
            A = self.g[x] * self.t ** self.chi[x]
            M = M @ (A if e == 1 else np.linalg.inv(A))
        return M

    def elt(self, p):
        M = np.zeros((self.n, self.n), dtype=complex)
        for w, c in p.items():
            M = M + c * self.word(w)
        return M


def rank(M, tol=1e-7):
    if M.size == 0:
        return 0
    s = np.linalg.svd(M, compute_uv=False)
    return int((s > tol * max(1.0, s[0])).sum())


def full_h1(V, E, R):
    n = R.n
    I = np.eye(n)
    D1 = np.vstack([R.word(((x, 1),)) - I for x in V])
    D2 = np.vstack([np.hstack([R.elt(fox(relator(a, b, l), x)) for x in V])
                    for (a, b), l in E.items()])
    return n * len(V) - rank(D1) - rank(D2)


def g1(x):
    return el(((x, 1),))


def minus_one(x):
    return add(g1(x), scal(-1, ONE))


def one_minus(x):
    return add(ONE, scal(-1, g1(x)))


def reduced_h1(V, E, chi, R, drop=()):
    """Dimension of coker of the dead-cut Laplacian; None if a hypothesis fails."""
    n = R.n
    liv = [x for x in V if chi[x] != 0]
    dead = [x for x in V if chi[x] == 0]
    nbr = {x: [] for x in V}
    for (a, b), l in E.items():
        nbr[a].append((b, l, (a, b)))
        nbr[b].append((a, l, (a, b)))

    def isdead(a, b, l):
        return l % 2 == 0 and l >= 4 and chi[a] + chi[b] == 0

    # components of Liv^chi
    comp = {x: x for x in liv}

    def find(x):
        while comp[x] != x:
            x = comp[x]
        return x

    units = []  # factors the derivation inverts
    for x in liv:
        units.append(minus_one(x))
    for (a, b), l in E.items():
        if chi[a] and chi[b] and not isdead(a, b, l):
            comp[find(a)] = find(b)
            du = add(fox(prod_word(a, b, l), a), scal(-1, fox(prod_word(b, a, l), a)))
            units.append(du)  # f_e = (1 - b)^{-1}-free part; (b - 1) is already a unit
    blocks = sorted({find(x) for x in liv})
    pos = {c: i for i, c in enumerate(blocks)}
    # dead-vertex elimination
    choice = {}
    for w in dead:
        opts = [(x, l, e) for (x, l, e) in nbr[w] if chi[x] != 0]
        if not opts:
            return None, "not dominant"
        choice[w] = opts[0]
    alpha, beta = {}, {}
    for w, (u, l, e) in choice.items():
        k = l // 2
        alpha[w] = mul(one_minus(u), S(k, ((w, 1), (u, 1))))
        beta[w] = mul(minus_one(w), S(k, ((u, 1), (w, 1))))
        units.append(alpha[w])
    for p in units:
        if abs(np.linalg.det(R.elt(p))) < 1e-9:
            return None, "specialization kills a unit"
    rels = []  # (matrix g, block a, block b): relation N g (e_a - e_b)
    for (a, b), l in E.items():
        if chi[a] and chi[b]:
            if isdead(a, b, l):
                k = l // 2
                g = R.elt(mul(S(k, ((a, 1), (b, 1))), minus_one(a)))
                rels.append((g, find(a), find(b), "dead"))
            continue
        if chi[a] == 0 and chi[b] == 0:
            w, x = a, b
            aw = R.elt(fox(relator(w, x, l), w))
            uw = choice[w][0]
            g = aw @ np.linalg.inv(R.elt(alpha[w])) @ R.elt(beta[w]) @ R.elt(minus_one(uw))
            # the x-part is carried by the other chosen row; the pair is one relation
            rels.append((g, find(uw), find(choice[x][0]), "dd"))
            continue
        w, x = (a, b) if chi[a] == 0 else (b, a)
        if choice[w][2] == (a, b):
            continue  # the eliminating row itself
        k2 = l // 2
        g = R.elt(mul(mul(minus_one(w), S(k2, ((x, 1), (w, 1)))), minus_one(x)))
        rels.append((g, find(x), find(choice[w][0]), "virt"))
    rels = [x[:3] for x in rels if x[3] not in drop]
    r = len(blocks)
    if not rels:
        return n * (r - 1), "ok"
    L = np.zeros((n * len(rels), n * r), dtype=complex)
    for i, (g, ca, cb) in enumerate(rels):
        L[i * n:(i + 1) * n, pos[ca] * n:(pos[ca] + 1) * n] += g
        L[i * n:(i + 1) * n, pos[cb] * n:(pos[cb] + 1) * n] -= g
    return n * (r - 1) - rank(L), "ok"


def random_instance(rng):
    nv = rng.randint(3, 6)
    V = [f"x{i}" for i in range(nv)]
    E = {}
    for a, b in itertools.combinations(V, 2):
        if rng.random() < 0.7:
            E[(a, b)] = rng.choice([2, 2, 3, 4, 4, 4, 5, 6, 6, 8])
    # chi constant on odd-edge classes
    cls = {x: x for x in V}

    def find(x):
        while cls[x] != x:
            x = cls[x]
        return x

    for (a, b), l in E.items():
        if l % 2:
            cls[find(a)] = find(b)
    val = {}
    for x in V:
        c = find(x)
        if c not in val:
            val[c] = rng.choice([1, 1, -1, -1, 2, -2, 0])
    chi = {x: val[find(x)] for x in V}
    if all(c == 0 for c in chi.values()):
        return None
    # m' | l on edges
    mprime = {}
    for e, l in E.items():
        divs = [d for d in range(2, l + 1) if l % d == 0]
        mprime[e] = rng.choice(divs)
    lam = {c: rng.choice([1, -1, 1j, complex(math.cos(1), math.sin(1))]) for c in val}
    return V, E, chi, mprime, {x: lam[find(x)] for x in V}


def run_numeric(trials, seed=20260917):
    rng = random.Random(seed)
    nprng = np.random.default_rng(seed)
    stats = {"compared": 0, "agree": 0, "skipped": 0, "nonzero_h1": 0,
             "with_dead_edges": 0, "with_dead_vertices": 0}
    bad = []
    while stats["compared"] < trials:
        inst = random_instance(rng)
        if inst is None:
            continue
        V, E, chi, mprime, lam = inst
        gens = coxeter_rep(V, mprime, nprng)
        gens = {x: lam[x] * gens[x] for x in V}
        t = complex(0.6 + 0.5 * rng.random(), 0.3 + 0.4 * rng.random())
        R = Rep(gens, chi, t)
        red_dim, why = reduced_h1(V, E, chi, R)
        if red_dim is None:
            stats["skipped"] += 1
            continue
        full = full_h1(V, E, R)
        stats["compared"] += 1
        stats["agree"] += int(full == red_dim)
        stats["nonzero_h1"] += int(full > 0)
        stats["with_dead_edges"] += int(any(l % 2 == 0 and l >= 4 and chi[a] and chi[b]
                                            and chi[a] + chi[b] == 0
                                            for (a, b), l in E.items()))
        stats["with_dead_vertices"] += int(any(c == 0 for c in chi.values()))
        if full != red_dim:
            bad.append((V, E, chi, mprime, full, red_dim))
        for kind in ("dead", "virt", "dd"):
            alt = reduced_h1(V, E, chi, R, drop=(kind,))[0]
            key = "control_drop_" + kind + "_changes_answer"
            stats[key] = stats.get(key, 0) + int(alt != full)
    return stats, bad


def kq_check():
    """K_q, q odd, chi = (1,1,-1,-1): full and reduced dimensions agree."""
    out = []
    for q in (3, 5, 7):
        V = ["a", "b", "c", "e"]
        E = {("a", "b"): 2, ("c", "e"): 2, ("a", "c"): 4, ("b", "c"): 4,
             ("b", "e"): 4, ("a", "e"): 2 * q}
        chi = {"a": 1, "b": 1, "c": -1, "e": -1}
        rng = np.random.default_rng(q)
        for m in (2, q):
            mprime = {e: (m if l == 2 * q else 2) for e, l in E.items()}
            gens = coxeter_rep(V, mprime, rng)
            R = Rep(gens, chi, complex(0.7, 0.4))
            out.append((q, m, full_h1(V, E, R), reduced_h1(V, E, chi, R)[0]))
    return out


if __name__ == "__main__":
    print("(1) Fox row formulas, 2 <= l <= 14:", check_fox_formulas())
    print("(2) living-edge factors have one +-1 word per level:", check_levels())
    stats, bad = run_numeric(400)
    print("(3) random reduction check:", stats)
    print("    disagreements:", len(bad))
    for b in bad[:5]:
        print("   ", b)
    print("(4) K_q odd, (q, m', dim H_1 full, dim coker reduced):", kq_check())
