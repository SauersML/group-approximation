#!/usr/bin/env python3
"""Exhaustive search for aperiodic sub-SFTs of quasigroup spacetimes.

X_* = {x in Q^(Z^2) : x(z+e2) = x(z) * x(z+e1)}, (Q,*) a finite quasigroup.
Every sub-SFT of X_* is Omega(A) = {x in X_* : every length-L window of every row lies in A}
for some L and some A subset Q^L (a pattern on a finite shape is determined by a row segment below it).
Rows evolve by F(r)_i = r_i * r_(i+1).

Facts used (see the -proof.md artifact):
 (P) Omega(A) has a periodic point iff some F-cycle C of spatially periodic rows has all its
     cyclic L-windows in A, i.e. W_C subset A.
 (E) Omega(A) is empty iff Z_n(A) = {r : F^t r in Z_0(A) for 0<=t<=n} is empty for some n.
 Monotonicity: A subset A' => Omega(A) subset Omega(A').
So "no nonempty aperiodic Omega(A) for this (Q,*,L)" follows once every A that avoids all edges W_C
(C of period <= P) has Omega(A) empty.  Branch and bound over (IN, OUT) assignments of words.

Usage: search.py k L P NMAX [--all-squares]
"""
import sys, itertools, time
import numpy as np

sys.setrecursionlimit(100000)


# ---------------------------------------------------------------- quasigroups
def latin_squares(k):
    rows = list(itertools.permutations(range(k)))
    out = []

    def rec(sq):
        if len(sq) == k:
            out.append(tuple(sq))
            return
        for r in rows:
            if all(r[j] != s[j] for s in sq for j in range(k)):
                rec(sq + [r])

    rec([])
    return out


def iso_reps(k):
    """One Latin square per isomorphism class of quasigroups (simultaneous relabelling)."""
    seen, reps = set(), []
    for sq in latin_squares(k):
        if sq in seen:
            continue
        reps.append(sq)
        for p in itertools.permutations(range(k)):
            inv = [0] * k
            for a in range(k):
                inv[p[a]] = a
            t = tuple(tuple(p[sq[inv[a]][inv[b]]] for b in range(k)) for a in range(k))
            seen.add(t)
    return reps


# ---------------------------------------------------------------- periodic cycles (fact P)
def cycle_edges(T, k, L, P):
    """Inclusion-minimal sets W_C over all F-cycles C of rows of period p <= P."""
    Tn = np.array(T, dtype=np.int64)
    kL = k ** L
    edges = set()
    for p in range(1, P + 1):
        n = k ** p
        digits = np.zeros((n, p), dtype=np.int64)
        v = np.arange(n, dtype=np.int64)
        for i in range(p):
            digits[:, i] = v % k
            v //= k
        img = Tn[digits, np.roll(digits, -1, axis=1)]
        pw = k ** np.arange(p, dtype=np.int64)
        f = img @ pw
        # windows: word index sum_j r_(i+j) k^(L-1-j)
        win = np.zeros((n, p), dtype=np.int64)
        for j in range(L):
            win = win * k + np.roll(digits, -j, axis=1)
        cyc = np.ones(n, dtype=bool)
        while True:
            nxt = np.zeros(n, dtype=bool)
            nxt[f[cyc]] = True
            if (nxt == cyc).all():
                break
            cyc = nxt
        done = np.zeros(n, dtype=bool)
        for s in np.nonzero(cyc)[0]:
            if done[s]:
                continue
            mask = 0
            r = s
            while not done[r]:
                done[r] = True
                for w in set(win[r].tolist()):
                    mask |= 1 << w
                r = f[r]
            edges.add(mask)
    edges = sorted(edges, key=lambda m: bin(m).count("1"))
    minimal = []
    for e in edges:
        if not any((m & e) == m for m in minimal):
            minimal.append(e)
    return minimal, kL


# ---------------------------------------------------------------- level automata (fact E)
def trim_minimize(delta, k):
    """delta: list of k-tuples (-1 = undefined). Keep states on bi-infinite paths, merge equal follower sets."""
    m = len(delta)
    alive = [True] * m
    indeg = [0] * m
    outdeg = [0] * m
    for s in range(m):
        for t in delta[s]:
            if t >= 0:
                outdeg[s] += 1
                indeg[t] += 1
    preds = [[] for _ in range(m)]
    for s in range(m):
        for t in delta[s]:
            if t >= 0:
                preds[t].append(s)
    stack = [s for s in range(m) if indeg[s] == 0 or outdeg[s] == 0]
    while stack:
        s = stack.pop()
        if not alive[s]:
            continue
        alive[s] = False
        for t in delta[s]:
            if t >= 0 and alive[t]:
                indeg[t] -= 1
                if indeg[t] == 0:
                    stack.append(t)
        for q in preds[s]:
            if alive[q]:
                outdeg[q] -= 1
                if outdeg[q] == 0:
                    stack.append(q)
    live = [s for s in range(m) if alive[s]]
    if not live:
        return []
    idx = {s: i for i, s in enumerate(live)}
    d = [tuple(idx[t] if t >= 0 and alive[t] else -1 for t in delta[s]) for s in live]
    # Moore refinement
    cls = [0] * len(d)
    ncls = 1
    while True:
        sig = {}
        new = []
        for i in range(len(d)):
            key = (cls[i],) + tuple(cls[t] if t >= 0 else -1 for t in d[i])
            if key not in sig:
                sig[key] = len(sig)
            new.append(sig[key])
        if len(sig) == ncls:
            break
        cls, ncls = new, len(sig)
    rep = {}
    for i in range(len(d)):
        rep.setdefault(cls[i], i)
    return [tuple(cls[t] if t >= 0 else -1 for t in d[rep[c]]) for c in range(ncls)]


def level_run(T, k, L, A, nmax, cap=60000):
    """Iterate G_n. Returns ('empty', n) , ('alive', nmax, size) or ('cap', n, size)."""
    kl1 = k ** (L - 1)
    G = [tuple(-1 for _ in range(k))]  # one-state full-shift presentation
    G = [tuple(0 for _ in range(k))]
    for n in range(nmax + 1):
        mG = len(G)
        if kl1 * mG > cap * 4:
            return ("cap", n, mG)
        delta = []
        for u in range(kl1):
            b = u % k
            for s in range(mG):
                row = []
                ds = G[s]
                for a in range(k):
                    w = u * k + a
                    t = ds[T[b][a]] if (A >> w) & 1 else -1
                    row.append(((w % kl1) * mG + t) if t >= 0 else -1)
                delta.append(tuple(row))
        G = trim_minimize(delta, k)
        if not G:
            return ("empty", n)
        if len(G) > cap:
            return ("cap", n, len(G))
    return ("alive", nmax, len(G), G)


def cycle_rows(G, k, maxlen=200):
    """For each state, the label word of a shortest closed walk through it (spatially periodic rows of Z_n)."""
    out = set()
    for s0 in range(len(G)):
        prev = {s0: None}
        frontier = [s0]
        found = None
        depth = 0
        while frontier and found is None and depth < maxlen:
            depth += 1
            nf = []
            for s in frontier:
                for a in range(k):
                    t = G[s][a]
                    if t < 0:
                        continue
                    if t == s0:
                        found = (s, a)
                        break
                    if t not in prev:
                        prev[t] = (s, a)
                        nf.append(t)
                if found:
                    break
            frontier = nf
        if found:
            word = [found[1]]
            s = found[0]
            while s != s0:
                ps, a = prev[s]
                word.append(a)
                s = ps
            out.add(tuple(reversed(word)))
    return sorted(out, key=len)


def legal_cycle(T, k, L, A, row, maxsteps=100000):
    """Iterate F on the periodic row; return window mask of the eventual F-cycle if every row stays legal."""
    p = len(row)
    seen = {}
    rows = []
    r = tuple(row)
    while r not in seen:
        for i in range(p):
            w = 0
            for j in range(L):
                w = w * k + r[(i + j) % p]
            if not (A >> w) & 1:
                return None
        seen[r] = len(rows)
        rows.append(r)
        if len(rows) > maxsteps:
            return None
        r = tuple(T[r[i]][r[(i + 1) % p]] for i in range(p))
    mask = 0
    for q in rows[seen[r]:]:
        for i in range(p):
            w = 0
            for j in range(L):
                w = w * k + q[(i + j) % p]
            mask |= 1 << w
    return mask


def language(G, k, L):
    """Bitmask of length-L words labelling paths of the trimmed graph G (= L-words of the presented shift)."""
    mask = 0
    frontier = [(s, 0) for s in range(len(G))]
    for _ in range(L):
        nf = set()
        for s, w in frontier:
            for a in range(k):
                t = G[s][a]
                if t >= 0:
                    nf.add((t, w * k + a))
        frontier = nf
    for _, w in frontier:
        mask |= 1 << w
    return mask


# ---------------------------------------------------------------- branch and bound
def search(T, k, L, P, nmax, nquick=8, log=None):
    edges, kL = cycle_edges(T, k, L, P)
    full = (1 << kL) - 1
    stats = {"nodes": 0, "empty_prune": 0, "leaves": 0, "maxlevel": 0, "certified": 0, "lang_prune": 0}
    cands = []

    def rec(IN, OUT):
        stats["nodes"] += 1
        if log and stats["nodes"] % 2000 == 0:
            log("progress nodes=%d %s" % (stats["nodes"], stats))
        Amax = full & ~OUT
        r = level_run(T, k, L, Amax, nquick)
        if r[0] == "empty":
            stats["empty_prune"] += 1
            stats["maxlevel"] = max(stats["maxlevel"], r[1])
            return
        if r[0] == "alive":
            lang = language(r[3], k, L)
            if IN & ~lang:
                stats["lang_prune"] += 1
                return  # equivalent to an earlier sibling branch
            if Amax & ~lang:
                OUT |= Amax & ~lang
                Amax = lang
        # an edge inside Amax not yet hit by OUT
        best = None
        for e in edges:
            if e & OUT == 0:
                und = e & ~IN
                if und == 0:
                    return  # periodic point already forced
                c = bin(und).count("1")
                if best is None or c < best[0]:
                    best = (c, und)
                    if c == 1:
                        break
        if best is None:
            stats["leaves"] += 1
            r = level_run(T, k, L, Amax, nmax)
            if r[0] == "empty":
                stats["maxlevel"] = max(stats["maxlevel"], r[1])
                return
            if r[0] == "alive":
                newe = set()
                for row in cycle_rows(r[3], k):
                    m = legal_cycle(T, k, L, Amax, row)
                    if m is not None:
                        newe.add(m)
                if newe:
                    stats["certified"] += 1
                    for m in newe:
                        if not any((e & m) == e for e in edges):
                            edges.append(m)
                    edges.sort(key=lambda m: bin(m).count("1"))
                    stats["leaves"] -= 1
                    return rec(IN, OUT)
            cands.append((Amax, r[:3]))
            if log:
                log("CANDIDATE A=%x %s" % (Amax, r[:3]))
            return
        und = best[1]
        words = [w for w in range(kL) if (und >> w) & 1]
        inacc = 0
        for w in words:
            rec(IN | inacc, OUT | (1 << w))
            inacc |= 1 << w

    rec(0, 0)
    return edges, stats, cands


def main():
    k, L, P, nmax = map(int, sys.argv[1:5])
    allsq = "--all-squares" in sys.argv
    squares = latin_squares(k) if allsq else iso_reps(k)
    t0 = time.time()
    print("k=%d L=%d P=%d nmax=%d squares=%d" % (k, L, P, nmax, len(squares)), flush=True)
    total_c = 0
    for sq in squares:
        edges, st, cands = search(sq, k, L, P, nmax, log=lambda s: print("   ", s, flush=True))
        total_c += len(cands)
        print("square %s edges=%d nodes=%d emptyprune=%d leaves=%d certified=%d maxlevel=%d candidates=%d t=%.1fs"
              % (sq, len(edges), st["nodes"], st["empty_prune"], st["leaves"], st["certified"], st["maxlevel"], len(cands),
                 time.time() - t0), flush=True)
    print("TOTAL candidates:", total_c)


if __name__ == "__main__":
    main()
