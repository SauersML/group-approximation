#!/usr/bin/env python3
"""Kernel census for Hall hosts of one-sided free HNN extensions.

Setting (bh-embeddability-survives-decidable-edge-hnn, sub-case chi >= 0):
  G = F *_{phi : A -> B},  F = <x,y> free,  [F:A] = k finite,  B of infinite index.
  Host H = Y *_{Phi : C_1 -> C_2},  Y = F * <b>,  [Y:C_i] = m,
  C_1 cap F = A (domain exact, base F-component of Sigma_1 is Delta = Sch(F,A)),
  C_2 cap F = Bbar = B * L_0 of index n in F,  Phi|_A = phi.
  theta : G -> H,  t -> s,  F -> F.

Designs for S = Phi^{-1}(L_0):
  wedge : S = b pi b^{-1}, pi <= Stab_F(u_0) in the F-component Sigma_out of u_0 = 0.b
  naive : S spanned by random C_1 Schreier-basis elements (not in A)

Computations:
  (1) exact decision of two-peak kernels  t f1 t^-1 f2 t f3 t^-1 f4  via the pair graph
      of the Stallings graph Gamma_Q, Q = Phi^{-1}(Bbar) = A * S;  every hit is turned into
      an explicit G-reduced word and verified by Britton reduction in H;
  (2) brute-force census of short cyclically G-reduced words with >= 2 peaks.

Letters: 1 = x, 2 = y, 3 = b, negatives are inverses.  Standard library only.
Usage: python3 hall_kernel_census.py [seeds] [maxlen]
"""
import random
import sys
from collections import deque
from itertools import product

FL = (1, -1, 2, -2)
YL = (1, -1, 2, -2, 3, -3)


def red(w):
    st = []
    for a in w:
        if st and st[-1] == -a:
            st.pop()
        else:
            st.append(a)
    return st


def inv(w):
    return [-a for a in reversed(w)]


def fwords(maxlen):
    out = [[]]
    layer = [[]]
    for _ in range(maxlen):
        nl = []
        for w in layer:
            for a in FL:
                if w and w[-1] == -a:
                    continue
                nl.append(w + [a])
        out += nl
        layer = nl
    return out


# ---------- permutation representations (right actions) ----------

def rand_perm(pts, rng):
    img = list(pts)
    rng.shuffle(img)
    return dict(zip(pts, img))


def full_rep(perms):
    """perms: dict letter(+) -> dict v->v ; add inverses."""
    rep = {}
    for g, p in perms.items():
        rep[g] = p
        rep[-g] = {u: v for v, u in p.items()}
    return rep


def read(rep, w, v):
    for a in w:
        v = rep[a].get(v)
        if v is None:
            return None
    return v


def connected(rep, verts, letters):
    verts = list(verts)
    seen = {verts[0]}
    dq = deque([verts[0]])
    while dq:
        v = dq.popleft()
        for a in letters:
            u = rep[a].get(v)
            if u is not None and u not in seen:
                seen.add(u)
                dq.append(u)
    return len(seen) == len(verts)


# ---------- Stallings folding ----------

def stallings(gens):
    """Folded graph of <gens>, base 0.  Returns rep (letter -> partial dict) on 0..V-1."""
    par = []
    out = []

    def new():
        par.append(len(par))
        out.append({})
        return len(par) - 1

    def find(v):
        while par[v] != v:
            par[v] = par[par[v]]
            v = par[v]
        return v

    pending = []

    def add(v, a, u):
        v, u = find(v), find(u)
        for (p, c, q) in ((v, a, u), (u, -a, v)):
            if c in out[p]:
                q2 = find(out[p][c])
                if q2 != q:
                    pending.append((q, q2))
            else:
                out[p][c] = q

    new()
    for w in gens:
        w = red(w)
        v = 0
        for i, a in enumerate(w):
            u = 0 if i == len(w) - 1 else new()
            add(v, a, u)
            v = u
    while pending:
        u, v = pending.pop()
        u, v = find(u), find(v)
        if u == v:
            continue
        par[v] = u
        ev = out[v]
        out[v] = {}
        for c, q in ev.items():
            add(u, c, q)
    roots = sorted({find(v) for v in range(len(par))}, key=lambda r: (r != find(0), r))
    idx = {r: i for i, r in enumerate(roots)}
    rep = {a: {} for a in YL}
    for r in roots:
        for c, q in out[r].items():
            rep[c][idx[r]] = idx[find(q)]
    return rep, len(roots)


def nedges(rep, letters=(1, 2, 3)):
    return sum(len(rep[a]) for a in letters)


# ---------- Schreier trees and bases ----------

class Cover:
    """Transitive Y-action on 0..m-1; C = Stab(0).  tree phases fix the spanning tree."""

    def __init__(self, rep, m, phases):
        self.rep, self.m = rep, m
        self.p = {0: []}
        self.tree = set()
        for allowed in phases:
            dq = deque(self.p.keys())
            while dq:
                v = dq.popleft()
                for a in YL:
                    u = rep[a].get(v)
                    if u is None or u in self.p or not allowed(v, a, u):
                        continue
                    self.p[u] = self.p[v] + [a]
                    self.tree.add((v, a) if a > 0 else (u, -a))
                    dq.append(u)
        assert len(self.p) == m, "tree does not span"
        self.basis = []  # list of (v, g)
        self.bidx = {}
        for v in range(m):
            for g in (1, 2, 3):
                if (v, g) not in self.tree:
                    self.bidx[(v, g)] = len(self.basis)
                    self.basis.append((v, g))

    def elem(self, i):
        v, g = self.basis[i]
        return red(self.p[v] + [g] + inv(self.p[self.rep[g][v]]))

    def member(self, w):
        return read(self.rep, w, 0) == 0

    def rewrite(self, w):
        """w in C -> list of signed basis indices (1-based sign-coded as (i, e))."""
        v = 0
        out = []
        for a in w:
            if a > 0:
                u = self.rep[a][v]
                if (v, a) in self.bidx:
                    out.append((self.bidx[(v, a)], 1))
            else:
                u = self.rep[a][v]
                if (u, -a) in self.bidx:
                    out.append((self.bidx[(u, -a)], -1))
            v = u
        assert v == 0
        return out


# ---------- random input (A, B, phi) and host ----------

def rand_transitive_F(pts, rng):
    while True:
        rep = full_rep({1: rand_perm(pts, rng), 2: rand_perm(pts, rng)})
        if connected(rep, pts, FL):
            return rep


def extend_perm(part, pts, rng):
    """extend a partial injection part (dict) to a permutation of pts"""
    dom = [v for v in pts if v not in part]
    img = [v for v in pts if v not in set(part.values())]
    rng.shuffle(img)
    p = dict(part)
    p.update(zip(dom, img))
    return p


def rand_B(rank, rng, lo=2, hi=4):
    """random infinite-index B <= F of given rank; returns folded core rep and size"""
    while True:
        gens = [red([rng.choice(FL) for _ in range(rng.randint(lo, hi))]) for _ in range(rank)]
        rep, V = stallings(gens)
        E = nedges(rep, (1, 2))
        if E - V + 1 != rank:
            continue
        if all(len(rep[a]) == V for a in (1, 2)):
            continue  # finite index
        return rep, V


class Host:
    def __init__(self, rng, k=2, extra_n=1, m=None, cout=None, design="wedge"):
        self.k = k
        # Delta : transitive F-action on 0..k-1, A = Stab(0)
        delta = list(range(k))
        drep = rand_transitive_F(delta, rng)
        self.drep = drep
        # B : rank k+1, infinite index; Bbar = completion on n vertices
        brep, nb = rand_B(k + 1, rng)
        self.brep = brep
        n = nb + extra_n
        self.n = n
        base2 = list(range(n))
        while True:
            px = extend_perm({v: u for v, u in brep[1].items()}, base2, rng)
            py = extend_perm({v: u for v, u in brep[2].items()}, base2, rng)
            b2 = full_rep({1: px, 2: py})
            if connected(b2, base2, FL):
                break
        L0 = n - k
        if cout is None:
            cout = max(L0, 2)
        if m is None:
            m = max(k + cout + 1, n + 1)
        assert m >= k + cout and m >= n
        self.m = m
        pts = list(range(m))
        # Sigma_1
        so = list(range(k, k + cout))
        rest1 = list(range(k + cout, m))
        while True:
            x1, y1 = dict(drep[1]), dict(drep[2])
            srep = rand_transitive_F(so, rng)
            x1.update(srep[1]); y1.update(srep[2])
            if rest1:
                rx, ry = rand_perm(rest1, rng), rand_perm(rest1, rng)
                x1.update(rx); y1.update(ry)
            bp = rand_perm(pts, rng)
            # force 0.b = k (= u_0)
            j = [v for v in pts if bp[v] == k][0]
            bp[j], bp[0] = bp[0], k
            r1 = full_rep({1: x1, 2: y1, 3: bp})
            if connected(r1, pts, YL):
                break
        inD = set(delta)
        inO = set(so)
        ph1 = [lambda v, a, u: v in inD and u in inD and abs(a) < 3,
               lambda v, a, u: v == 0 and a == 3,
               lambda v, a, u: v in inO and u in inO and abs(a) < 3,
               lambda v, a, u: True]
        self.S1 = Cover(r1, m, ph1)
        # Sigma_2
        rest2 = list(range(n, m))
        while True:
            x2, y2 = dict(px), dict(py)
            if rest2:
                x2.update(rand_perm(rest2, rng)); y2.update(rand_perm(rest2, rng))
            r2 = full_rep({1: x2, 2: y2, 3: rand_perm(pts, rng)})
            if connected(r2, pts, YL):
                break
        core = {(v, a) for a in (1, 2) for v in brep[a]}
        core |= {(u, -a) for a in (1, 2) for v, u in brep[a].items()}
        ph2 = [lambda v, a, u: (v, a) in core,
               lambda v, a, u: v < n and u < n and abs(a) < 3,
               lambda v, a, u: True]
        self.S2 = Cover(r2, m, ph2)
        # classify bases
        S1, S2 = self.S1, self.S2
        Abas = [i for i, (v, g) in enumerate(S1.basis) if v in inD and g < 3]
        Obas = [i for i, (v, g) in enumerate(S1.basis) if v in inO and g < 3]
        Bbas = [i for i, (v, g) in enumerate(S2.basis) if (v, g) in core]
        L0bas = [i for i, (v, g) in enumerate(S2.basis) if v < n and g < 3 and (v, g) not in core]
        assert len(Abas) == k + 1 and len(Bbas) == k + 1 and len(L0bas) == L0, (len(Abas), len(Bbas), len(L0bas))
        # Phi : C_1 basis -> C_2 basis (signed)
        phi = {}
        bb = Bbas[:]
        rng.shuffle(bb)
        for i, j in zip(Abas, bb):
            phi[i] = (j, 1)
        others1 = [i for i in range(len(S1.basis)) if i not in phi]
        if design == "wedge":
            src = rng.sample(Obas, L0)
        else:
            src = rng.sample(others1, L0)
        for i, j in zip(src, L0bas):
            phi[i] = (j, rng.choice((1, -1)))
        rem1 = [i for i in others1 if i not in phi]
        rem2 = [j for j in range(len(S2.basis)) if j not in set(Bbas) | set(L0bas)]
        rng.shuffle(rem2)
        for i, j in zip(rem1, rem2):
            phi[i] = (j, rng.choice((1, -1)))
        assert len(phi) == len(S1.basis) == len(S2.basis)
        self.phi = phi
        self.phiinv = {j: (i, e) for i, (j, e) in phi.items()}
        self.Sgen = [S1.elem(i) for i in src]
        self.Agen = [S1.elem(i) for i in Abas]
        self.design = design

    # --- maps ---
    def Phi(self, w):
        out = []
        for i, e in self.S1.rewrite(red(w)):
            j, s = self.phi[i]
            el = self.S2.elem(j)
            out += el if e * s > 0 else inv(el)
        return red(out)

    def Phiinv(self, w):
        out = []
        for j, e in self.S2.rewrite(red(w)):
            i, s = self.phiinv[j]
            el = self.S1.elem(i)
            out += el if e * s > 0 else inv(el)
        return red(out)

    def inA(self, f):
        return read(self.drep, f, 0) == 0

    def inB(self, f):
        return read(self.brep, red(f), 0) == 0

    def inBbar(self, f):
        return self.S2.member(f)

    def bbar_minus_b(self, length):
        """reduced products of <= length Bbar-basis elements (B-basis and L_0-basis), not in B"""
        gens = []
        for j, (v, g) in enumerate(self.S2.basis):
            if v < self.n and g < 3:
                el = self.S2.elem(j)
                gens += [el, inv(el)]
        out, layer = [], [[]]
        for _ in range(length):
            layer = [red(w + g) for w in layer for g in gens]
            out += layer
        seen, res = set(), []
        for w in out:
            if tuple(w) not in seen and not self.inB(w):
                seen.add(tuple(w))
                res.append(w)
        return res


# ---------- Britton reduction in H (s = letter 4) ----------

def britton_trivial(H, word):
    """word: list over +-1..+-3 and +-4 (=s).  True iff trivial in H."""
    st = [[]]  # alternating: Y-word, s-sign, Y-word, ...
    for a in word:
        if abs(a) != 4:
            st[-1] = red(st[-1] + [a])
            continue
        e = 1 if a > 0 else -1
        if len(st) >= 3 and st[-2] == -e:
            w = st[-1]
            if e == -1 and H.S1.member(w):  # s w s^-1, w in C_1
                st.pop(); st.pop()
                st[-1] = red(st[-1] + H.Phi(w))
                continue
            if e == 1 and H.S2.member(w):  # s^-1 w s, w in C_2
                st.pop(); st.pop()
                st[-1] = red(st[-1] + H.Phiinv(w))
                continue
        st.append(e)
        st.append([])
    return len(st) == 1 and not st[0]


def gword(ts, fs):
    """G-word t^{e1} f1 t^{e2} f2 ... as H-word"""
    w = []
    for e, f in zip(ts, fs):
        w.append(4 * e)
        w += f
    return w


def cyc_reduced(H, ts, fs):
    L = len(ts)
    for i in range(L):
        e, e2 = ts[i], ts[(i + 1) % L]
        if e == 1 and e2 == -1 and H.inA(fs[i]):
            return False
        if e == -1 and e2 == 1 and H.inB(fs[i]):
            return False
    return True


# ---------- (1) exact two-peak decision via the pair graph of Gamma_Q ----------

def two_peak_witness(H):
    """(v, w, z, pD) with v, w != 0 in Delta, z in Q minus A, p_v z p_w^-1 in Q; else None.

    Exact: the set of such z (for fixed v, w) is the label set of paths (q0, v') -> (q0, w')
    in the pair graph of Gamma_Q, a union of cosets of the loop group at (q0, v'); it lies in A
    iff every loop generator and every tree label to a target lies in A.
    """
    Q, V = stallings(H.Agen + H.Sgen)
    pD = {0: []}
    dq = deque([0])
    while dq:
        v = dq.popleft()
        for a in FL:
            u = H.drep[a][v]
            if u not in pD:
                pD[u] = pD[v] + [a]
                dq.append(u)
    img = {v: read(Q, pD[v], 0) for v in pD}
    assert len(set(img.values())) == H.k and None not in img.values(), "Delta not in Gamma_Q"
    back = {q: v for v, q in img.items()}
    for v in range(1, H.k):
        start = (0, img[v])
        lab = {start: []}
        dq = deque([start])
        gens = []
        while dq:
            P = dq.popleft()
            for a in YL:
                u1, u2 = Q[a].get(P[0]), Q[a].get(P[1])
                if u1 is None or u2 is None:
                    continue
                U = (u1, u2)
                if U not in lab:
                    lab[U] = lab[P] + [a]
                    dq.append(U)
                elif a > 0:
                    gens.append(red(lab[P] + [a] + inv(lab[U])))
        targets = [U for U in lab if U[0] == 0 and U[1] in back and back[U[1]] != 0]
        for U in targets:
            for z in [lab[U]] + [red(g + lab[U]) for g in gens]:
                if 3 in z or -3 in z or not H.inA(z):
                    return v, back[U[1]], z, pD
    return None


def explicit_two_peak(H, v, w, z, pD):
    f1 = pD[v]
    f3 = inv(pD[w])
    f2 = H.Phi(z)
    y = red(f1 + z + f3)
    f4 = inv(H.Phi(y))
    assert not any(abs(a) == 3 for a in f2 + f4), "Phi(Q) not in F"
    return (1, -1, 1, -1), (f1, f2, f3, f4)


# ---------- (2) brute-force census ----------

PATTERNS = {
    "2peak(+-+-)": (1, -1, 1, -1),
    "2peak(++--+-)": (1, 1, -1, -1, 1, -1),
    "3peak(+-+-+-)": (1, -1, 1, -1, 1, -1),
}


def census(H, maxlen, rng, cap=150000):
    words = fwords(maxlen)
    res = {}
    for name, ts in PATTERNS.items():
        L = len(ts)
        slots = []
        for i in range(L):
            e, e2 = ts[i], ts[(i + 1) % L]
            if e == 1 and e2 == -1:
                slots.append([f for f in words if not H.inA(f)])
            elif e == -1 and e2 == 1:
                slots.append([f for f in words if not H.inB(f)])
            else:
                slots.append(words)
        # a kernel element needs a first valley pinch: put a Bbar-minus-B word in the first valley
        vi = [i for i in range(L) if ts[i] == -1 and ts[(i + 1) % L] == 1][0]
        slots[vi] = H.bbar_minus_b(2)
        for i in range(L):
            if i != vi and ts[i] == -1 and ts[(i + 1) % L] == 1:
                slots[i] = slots[i] + [f for f in H.bbar_minus_b(1) if f not in slots[i]]
        total = 1
        for s in slots:
            total *= len(s)
        if total <= cap:
            it = product(*slots)
        else:
            it = (tuple(rng.choice(s) for s in slots) for _ in range(cap))
        tested = hits = 0
        example = None
        for fs in it:
            tested += 1
            if britton_trivial(H, gword(ts, fs)):
                hits += 1
                example = example or fs
        res[name] = (tested, hits, total > cap, example)
    return res


def main():
    seeds = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    k = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    brute = maxlen > 0
    for design in ("naive", "wedge"):
        n2 = nver = 0
        agg = {}
        for sd in range(seeds):
            rng = random.Random(1000 * sd + (design == "wedge") + 7 * k)
            H = Host(rng, k=k, extra_n=rng.choice((1, 2)), design=design)
            wit = two_peak_witness(H)
            if wit:
                n2 += 1
                ts, fs = explicit_two_peak(H, *wit)
                assert cyc_reduced(H, ts, fs), "witness not G-reduced"
                assert britton_trivial(H, gword(ts, fs)), "witness not in kernel"
                nver += 1
            if not brute:
                continue
            for name, (tested, hits, samp, ex) in census(H, maxlen, rng).items():
                a = agg.setdefault(name, [0, 0, 0])
                a[0] += tested; a[1] += hits; a[2] += bool(hits)
        print(f"design={design} k={k} hosts={seeds}: exact two-peak kernels in {n2} hosts "
              f"(explicit words Britton-verified: {nver})")
        for name, (t, h, nh) in agg.items():
            print(f"   census {name}, F-syllables <= {maxlen}: tested {t}, kernel words {h}, hosts with kernel {nh}")


if __name__ == "__main__":
    main()
