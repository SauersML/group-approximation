#!/usr/bin/env python3
"""Exact F_2 search for common right multiples a u = b v in F_2[M], M the positive monoid of
Thompson's group F, for a, b ranging over F_2[S] with S a homogeneous set of normal forms.

Normal forms of M: x_{i_1} ... x_{i_d} with i_1 <= ... <= i_d; relations x_j x_i = x_i x_{j+1}
for i < j.  By Guba (arXiv:2305.07113v4, Lemma `gig`) common multiples in K[F] may be taken in
K[M], and homogeneity lets them be taken homogeneous of one degree k.

For degree k and letter bound N, V = F_2[M_(k,N)].  Left multiplication by a nonzero element has
no kernel (K[F] has no zero divisors), so aV and bV both have dimension |V| and a common multiple
supported in M_(k,N) exists iff dim(aV + bV) < 2|V|.

Usage: ore_linalg.py SET KMAX [NOFFSET] [OUT.json]
  SET in {X2, S24, S35}; letter bound N = k + NOFFSET (default 3).
"""
import itertools, json, sys, time


def normalize(w):
    w = list(w)
    changed = True
    while changed:
        changed = False
        for k in range(len(w) - 1):
            if w[k] > w[k + 1]:
                j, i = w[k], w[k + 1]
                w[k], w[k + 1] = i, j + 1
                changed = True
    return tuple(w)


def guba_set(m, d):
    """S_(m+1, m+d+1): normal forms of degree d with i_t <= m + t - 1."""
    out = []
    for w in itertools.combinations_with_replacement(range(m + d), d):
        if all(w[t] <= m + t for t in range(d)):
            out.append(w)
    return out


SETS = {"X2": guba_set(2, 1), "S24": guba_set(1, 2), "S35": guba_set(2, 2)}


class XorBasis:
    """Incremental F_2 basis keyed by highest set bit."""

    def __init__(self):
        self.piv = {}

    def reduce(self, v):
        piv = self.piv
        while v:
            h = v.bit_length() - 1
            p = piv.get(h)
            if p is None:
                return v
            v ^= p
        return 0

    def insert(self, v):
        v = self.reduce(v)
        if v:
            self.piv[v.bit_length() - 1] = v
            return True
        return False

    def copy(self):
        c = XorBasis()
        c.piv = dict(self.piv)
        return c


def run(setname, kmax, noff, outpath):
    import os
    S = SETS[setname]
    nS = len(S)
    elems = list(range(1, 1 << nS))  # nonzero elements of F_2[S] as bitmasks
    pairs = [(a, b) for a in elems for b in elems if a < b]
    if os.environ.get("PAIRS_IN"):
        with open(os.environ["PAIRS_IN"]) as f:
            pairs = [tuple(p) for p in json.load(f)["unsolved"]]
    if os.environ.get("SHARD"):
        i, n = map(int, os.environ["SHARD"].split("/"))
        pairs = [p for p in pairs if p[0] % n == i]
    kmin = int(os.environ.get("KMIN", "0"))
    unsolved = set(pairs)
    solved_at = {}
    log = []
    for k in range(kmin, kmax + 1):
        if not unsolved:
            break
        N = k + noff
        t0 = time.time()
        V = list(itertools.combinations_with_replacement(range(N + 1), k))
        rows = {}
        img = [[0] * len(V) for _ in range(nS)]
        for si, s in enumerate(S):
            for ui, u in enumerate(V):
                nf = normalize(s + u)
                r = rows.get(nf)
                if r is None:
                    r = rows[nf] = len(rows)
                img[si][ui] = 1 << r
        def images(a):
            bits = [si for si in range(nS) if a >> si & 1]
            out = [0] * len(V)
            for ui in range(len(V)):
                v = 0
                for si in bits:
                    v ^= img[si][ui]
                out[ui] = v
            return out

        partners = {}
        for (a, b) in unsolved:
            partners.setdefault(a, []).append(b)
        newly = 0
        for a in sorted(partners):
            base = XorBasis()
            for v in images(a):
                base.insert(v)
            for b in sorted(partners[a]):
                B = base.copy()
                dep = False
                for v in images(b):
                    if not B.insert(v):
                        dep = True
                        break
                if dep:
                    solved_at[(a, b)] = k
                    newly += 1
        for p in list(solved_at):
            unsolved.discard(p)
        rec = {"k": k, "N": N, "|V|": len(V), "rows": len(rows), "solved_now": newly,
               "unsolved": len(unsolved), "secs": round(time.time() - t0, 2)}
        log.append(rec)
        print(json.dumps(rec), flush=True)
    hist = {}
    for p, k in solved_at.items():
        hist[k] = hist.get(k, 0) + 1
    result = {"set": setname, "S": S, "noffset": noff, "kmax": kmax, "pairs": len(pairs),
              "hist_min_degree": dict(sorted(hist.items())), "unsolved": sorted(unsolved),
              "solved": sorted([a, b, k, k + noff] for (a, b), k in solved_at.items()),
              "log": log}
    if outpath:
        with open(outpath, "w") as f:
            json.dump(result, f)
    print("HIST", json.dumps(result["hist_min_degree"]), "UNSOLVED", len(unsolved), flush=True)


if __name__ == "__main__":
    setname = sys.argv[1]
    kmax = int(sys.argv[2])
    noff = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    out = sys.argv[4] if len(sys.argv) > 4 else None
    assert normalize((1, 0)) == (0, 2), normalize((1, 0))
    assert len(SETS["S35"]) == 9 and len(SETS["S24"]) == 5 and len(SETS["X2"]) == 3
    run(setname, kmax, noff, out)
