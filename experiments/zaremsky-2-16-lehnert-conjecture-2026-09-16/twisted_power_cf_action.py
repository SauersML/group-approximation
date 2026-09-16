#!/usr/bin/env python3
"""Sanity checks for research/artifacts/twisted-power-cloning-cf-action-2026-09-16.md.

Groups V_(G,phi0,phi1): classes of labelled triple lists {(a_i, b_i, h_i)} with
refinement (a,b,h) -> (a0,b0,phi0 h), (a1,b1,phi1 h) and product
{(a_i,b_i,h_i)}{(b_i,c_i,k_i)} = {(a_i,c_i,h_i k_i)}.  F-type = order preserving.

Checks, for small finite G and endomorphism pairs with ker phi0 ∩ ker phi1 = 1:
  (L) Lemma M = 1 (exhaustive over the listed pairs).
  (R) the action on Omega_p is refinement invariant (random elements, points).
  (H) action of a product = composite of actions (random).
  (F) nontrivial random elements move some point of some Omega_p, p in P.
  (P) the decorated-stack pushdown simulation tracks the orbit point and its
      acceptance test agrees with "returns to the base point".
Single-threaded, deterministic seed, small output.
"""
import itertools
import random
import sys

random.seed(20260916)


# ---------------------------------------------------------------- finite groups
def cyclic(n):
    els = list(range(n))
    mul = [[(a + b) % n for b in els] for a in els]
    return els, mul


def elementary_abelian(r):
    els = list(range(2 ** r))
    mul = [[a ^ b for b in els] for a in els]
    return els, mul


def symmetric3():
    perms = list(itertools.permutations(range(3)))
    idx = {p: i for i, p in enumerate(perms)}
    # right-action composition p*q = "p then q"
    mul = [[idx[tuple(q[p[i]] for i in range(3))] for q in perms] for p in perms]
    return list(range(6)), mul


def group_data(els, mul):
    e = next(a for a in els if all(mul[a][b] == b for b in els))
    inv = [next(b for b in els if mul[a][b] == e) for a in els]
    return e, inv


def endomorphisms(els, mul, gens):
    """All endomorphisms, found by assigning images to generators and closing."""
    e, _ = group_data(els, mul)
    res = set()
    for imgs in itertools.product(els, repeat=len(gens)):
        f = {e: e}
        for g, im in zip(gens, imgs):
            f[g] = im
        changed = True
        ok = True
        while changed and ok:
            changed = False
            for a in list(f):
                for b in list(f):
                    c = mul[a][b]
                    v = mul[f[a]][f[b]]
                    if c in f:
                        if f[c] != v:
                            ok = False
                            break
                    else:
                        f[c] = v
                        changed = True
                if not ok:
                    break
        if ok and len(f) == len(els):
            if all(f[mul[a][b]] == mul[f[a]][f[b]] for a in els for b in els):
                res.add(tuple(f[a] for a in els))
    return sorted(res)


def compose(f, g):
    """apply f first, then g"""
    return tuple(g[f[a]] for a in range(len(f)))


# ------------------------------------------------------------- the M = 1 lemma
def semigroup(gens):
    S = set(gens)
    frontier = list(gens)
    while frontier:
        new = []
        for s in frontier:
            for t in gens:
                u = compose(s, t)
                if u not in S:
                    S.add(u)
                    new.append(u)
        frontier = new
    return S


def lemma_M(els, e, phi0, phi1):
    S = semigroup([phi0, phi1])
    E = [s for s in S if compose(s, s) == s]
    ident = tuple(els)
    S1 = list(S) + [ident]
    M = [h for h in els if all(t[s[h]] == e for t in E for s in S1)]
    return M, S, E


# ------------------------------------------------------------- triple lists
class Sys:
    def __init__(self, els, mul, phi0, phi1):
        self.els, self.mul = els, mul
        self.e, self.inv = group_data(els, mul)
        self.phi = {"0": phi0, "1": phi1}
        self.ident = tuple(els)

    def phi_word(self, u):
        f = self.ident
        for c in u:
            f = compose(f, self.phi[c])  # letters applied in order
        return f

    def refine(self, g, i):
        a, b, h = g[i]
        return g[:i] + [(a + "0", b + "0", self.phi["0"][h]), (a + "1", b + "1", self.phi["1"][h])] + g[i + 1:]

    def product(self, g, k):
        g, k = list(g), list(k)
        while True:
            changed = False
            for i, (a, b, h) in enumerate(g):
                if any(c != b and c.startswith(b) for (c, d, _) in k):
                    g = self.refine(g, i)
                    changed = True
                    break
            if changed:
                continue
            for i, (c, d, h) in enumerate(k):
                if any(b != c and b.startswith(c) for (a, b, _) in g):
                    k = self.refine(k, i)
                    changed = True
                    break
            if not changed:
                break
        kd = {c: (d, h) for (c, d, h) in k}
        return [(a, kd[b][0], self.mul[h][kd[b][1]]) for (a, b, h) in g]

    def inverse(self, g):
        return [(b, a, self.inv[h]) for (a, b, h) in g]

    # ---- action on Omega_p: representatives (h, x), (h,x) ~ (phi_p h, x p)
    def act(self, g, pt, p):
        h, x = pt
        php = self.phi_word(p)
        while not any(x.startswith(a) for (a, _, _) in g):
            h, x = php[h], x + p
        for (a, b, hi) in g:
            if x.startswith(a):
                u = x[len(a):]
                return (self.mul[h][self.phi_word(u)[hi]], b + u)
        raise AssertionError

    def equiv(self, pt1, pt2, p):
        (h1, x1), (h2, x2) = pt1, pt2
        if (len(x1) - len(x2)) % len(p):
            return False
        php = self.phi_word(p)
        L = max(len(x1), len(x2)) + len(p) * (len(self.els) + 1)
        while len(x1) < L:
            h1, x1 = php[h1], x1 + p
        while len(x2) < L:
            h2, x2 = php[h2], x2 + p
        return x1 == x2 and h1 == h2


def random_code(n):
    code = [""]
    while len(code) < n:
        i = random.randrange(len(code))
        w = code.pop(i)
        code[i:i] = [w + "0", w + "1"]
    return code  # lexicographic order preserved by construction


def random_element(S, n, ftype):
    A, B = random_code(n), random_code(n)
    if not ftype:
        random.shuffle(B)
    return [(a, b, random.choice(S.els)) for a, b in zip(A, B)]


def random_point(S, p):
    return (random.choice(S.els), "".join(random.choice("01") for _ in range(random.randrange(5))))


def idempotent_words(S):
    """one (shortest) word p for each idempotent phi_p of the semigroup <phi0,phi1>,
    found by breadth-first search over the finite semigroup (exact, no length cap)"""
    word_of = {}
    frontier = []
    for c in "01":
        f = S.phi[c]
        if f not in word_of:
            word_of[f] = c
            frontier.append(f)
    while frontier:
        new = []
        for f in frontier:
            for c in "01":
                g = compose(f, S.phi[c])  # word_of[f] + c
                if g not in word_of:
                    word_of[g] = word_of[f] + c
                    new.append(g)
        frontier = new
    return {f: w for f, w in word_of.items() if compose(f, f) == f}


# ---------------------------------------------------------------- pushdown sim
def pda_run(S, word, p, gens):
    """Decorated-stack simulation of the automaton of the artifact, section 5."""
    h = S.e
    stack = []  # list of (letter, decoration) from TOP to bottom, '#' implicit at bottom

    def decorate(w, below):
        # below = decoration of the letter just below w (identity if '#')
        out = []
        f = below
        for c in reversed(w):
            f = compose(S.phi[c], f)  # suffix from c: apply c first, then the rest
            out.append((c, f))
        return list(reversed(out))

    php = S.phi_word(p)
    for sym in word:
        g = gens[sym]
        L = max(len(a) for (a, _, _) in g)
        x = "".join(c for c, _ in stack)
        t1 = [(a, b, hi) for (a, b, hi) in g if len(x) > len(a) and x.startswith(a)]
        if t1:  # T1: pop a c_kappa, push b c_kappa
            (a, b, hi), = t1
            kappa = stack[len(a)][1]
            # the stored decoration must equal phi_u for u = x[len(a):]
            assert kappa == S.phi_word(x[len(a):])
            h = S.mul[h][kappa[hi]]
            rest = stack[len(a):]  # rest[0] is the letter c with decoration kappa
            stack = decorate(b, rest[0][1]) + rest
        else:  # T2: x is a prefix of a code word; pop x#, push (b u)#
            assert any(a.startswith(x) for (a, _, _) in g) and len(x) <= L
            m = 0
            xm = x
            while not any(xm.startswith(a) for (a, _, _) in g):
                m += 1
                xm = x + p * m
            (a, b, hi), = [(a, b, hi) for (a, b, hi) in g if xm.startswith(a)]
            u = xm[len(a):]
            hh = h
            for _ in range(m):
                hh = php[hh]
            h = S.mul[hh][S.phi_word(u)[hi]]
            stack = decorate(b + u, S.ident)
        # decoration invariant
        xs = "".join(c for c, _ in stack)
        for i, (c, f) in enumerate(stack):
            assert f == S.phi_word(xs[i:]), "decoration invariant broken"
    xs = "".join(c for c, _ in stack)
    kernel_ep = S.phi_word(p * len(S.els))  # e_p power with stabilised kernel
    accept = (kernel_ep[h] == S.e) and len(xs) % len(p) == 0 and xs == p * (len(xs) // len(p))
    return (h, xs), accept


def main():
    groups = {
        "Z2": (cyclic(2), [1]),
        "Z3": (cyclic(3), [1]),
        "Z4": (cyclic(4), [1]),
        "Z2^2": (elementary_abelian(2), [1, 2]),
        "Z2^3": (elementary_abelian(3), [1, 2, 4]),
        "S3": (symmetric3(), None),
    }
    total_pairs = 0
    for name, ((els, mul), gens) in groups.items():
        if gens is None:  # S3: generators (01) and (012)
            perms = list(itertools.permutations(range(3)))
            gens = [perms.index((1, 0, 2)), perms.index((1, 2, 0))]
        e, _ = group_data(els, mul)
        ends = endomorphisms(els, mul, gens)
        pairs = []
        for f0 in ends:
            for f1 in ends:
                if all(not (f0[h] == e and f1[h] == e) for h in els if h != e):
                    pairs.append((f0, f1))
        for (f0, f1) in pairs:
            M, Sg, E = lemma_M(els, e, f0, f1)
            assert M == [e], (name, f0, f1, M)
        total_pairs += len(pairs)
        print(f"[L] {name}: |End|={len(ends)}, injective-cloning pairs={len(pairs)}, M=1 for all")

        # dynamic checks on a sample of pairs
        sample = random.sample(pairs, min(len(pairs), 12))
        for (f0, f1) in sample:
            S = Sys(els, mul, f0, f1)
            P = idempotent_words(S)
            Pw = list(P.values())
            assert len(Pw) == len(E_of(S)), "every idempotent realised by a short word"
            for trial in range(25):
                ftype = trial % 2 == 0
                g = random_element(S, random.randrange(1, 6), ftype)
                k = random_element(S, random.randrange(1, 6), ftype)
                for p in Pw:
                    pt = random_point(S, p)
                    # (R) refinement invariance
                    g2 = S.refine(g, random.randrange(len(g)))
                    assert S.equiv(S.act(g, pt, p), S.act(g2, pt, p), p)
                    # (H) homomorphism
                    gk = S.product(g, k)
                    assert S.equiv(S.act(gk, pt, p), S.act(k, S.act(g, pt, p), p), p)
                    # inverse
                    assert S.equiv(S.act(S.inverse(g), S.act(g, pt, p), p), pt, p)
                # (F) faithfulness: nontrivial element (some label != e or a != b)
                nontriv = any(a != b or h != S.e for (a, b, h) in g)
                if nontriv:
                    moved = False
                    for p in Pw:
                        for (a, b, hi) in g:
                            for L in range(0, 7):
                                for u in itertools.product("01", repeat=L):
                                    u = "".join(u)
                                    for h in [S.e]:
                                        pt = (h, a + u)
                                        if not S.equiv(S.act(g, pt, p), pt, p):
                                            moved = True
                                            break
                                    if moved:
                                        break
                                if moved:
                                    break
                            if moved:
                                break
                        if moved:
                            break
                    # an element with all a_i = b_i and nontrivial labels must move a point
                    assert moved or not nontriv, ("faithfulness failed", name, f0, f1, g)
            # (P) pushdown simulation on random words over a random generating set
            gens_el = {}
            for s in range(3):
                gg = random_element(S, random.randrange(1, 5), False)
                gens_el[str(s)] = gg
                gens_el[str(s) + "'"] = S.inverse(gg)
            syms = list(gens_el)
            for p in Pw:
                for trial in range(30):
                    word = [random.choice(syms) for _ in range(random.randrange(0, 9))]
                    if trial % 3 == 0 and word:  # force some returning words w w^-1
                        inv = [s[:-1] if s.endswith("'") else s + "'" for s in reversed(word)]
                        word = word + inv
                    pt = (S.e, "")
                    for sym in word:
                        pt = S.act(gens_el[sym], pt, p)
                    (hh, xs), acc = pda_run(S, word, p, gens_el)
                    assert S.equiv((hh, xs), pt, p), "PDA point mismatch"
                    assert acc == S.equiv(pt, (S.e, ""), p), "PDA acceptance mismatch"
        print(f"[R,H,F,P] {name}: sampled {len(sample)} pairs OK")
    print(f"total injective-cloning endomorphism pairs checked for M=1: {total_pairs}")
    print("ALL CHECKS PASSED")


def E_of(S):
    Sg = semigroup([S.phi["0"], S.phi["1"]])
    return [s for s in Sg if compose(s, s) == s]


if __name__ == "__main__":
    sys.exit(main())
