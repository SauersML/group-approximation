#!/usr/bin/env python3
"""Independent machine check of the shared-pointer parity gadget firewall.

Target node: cancellative-incidence-patterns-do-not-force-domination
Artifact under check: research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md
Re-derivation: research/artifacts/cancellative-firewall-reverification-2026-09-17.md

Sections:
  1. Build the Theorem A pattern for k = 4, 8, 16, 32, check (L), (R), pointer sharing and the value XOR.
  2. Exact H(psi) by dynamic programming over the inputs.
  3. Exact H(x(o) | y_F) by full enumeration on small instances, against E #unrevealed = k (1 - 1/k)^R.
  4. Monte Carlo decoding on the full k = 4 and k = 8 instances.
  5. Theorem B made explicit: Evans embedding plus loop isotope for the k = 4 pattern (order 530 loop).
  6. Quadrangle closure: the gadget violates it; exhaustive check of the mod-3 theorem (Theorem C')
     on all 3-row cancellative patterns with |E| <= 4, and on random group patterns.
All logs base 2. Deterministic seeds. Writes verify_gadget.json next to this file.
"""
import itertools
import json
import math
import os
import random
import sys

import numpy as np

OUT = {}


def log2(x):
    return math.log(x, 2)


# ---------------------------------------------------------------- 1. the pattern

def gadget_pattern(k, R=None, n=None):
    t = int(round(log2(k)))
    assert 2 ** t == k
    if R is None:
        R = math.ceil(2 * k * math.log(k))
    if n is None:
        n = R if R % 2 == 1 else R + 1
    assert n % 2 == 1 and n >= R
    m = (n - 1) // 2
    E = ["P1", "P2", "P3"] + [("v", i) for i in range(n)]
    w = {}  # (codeword, position) -> site
    F = []
    for g in range(R):
        a, b, c = ("a", g), ("b", g), ("c", g)
        W1, W2, W3 = ("W1", g), ("W2", g), ("W3", g)
        F += [W1, W2, W3]
        for W, trip in ((W1, (a, b, c)), (W2, (b, c, a)), (W3, (c, a, b))):
            for P, s in zip(("P1", "P2", "P3"), trip):
                w[(W, P)] = s
        w[(W1, ("v", g % n))] = "x0"
        for i in range(1, m + 1):
            w[(W1, ("v", (g + i) % n))] = ("alpha", g, i)
            w[(W1, ("v", (g + m + i) % n))] = ("beta", g, i)
            w[(W2, ("v", (g + i - 1) % n))] = ("alpha", g, i)
            w[(W3, ("v", (g + m + i - 1) % n))] = ("beta", g, i)
        for l in range(1, m + 2):
            w[(W2, ("v", (g + m + l - 1) % n))] = ("gamma", g, l)
            w[(W3, ("v", (g + l - 2) % n))] = ("gamma", g, l)
    return dict(k=k, t=t, R=R, n=n, m=m, E=E, F=F, w=w)


def check_cancellation(pat):
    E, F, w = pat["E"], pat["F"], pat["w"]
    full = all((f, e) in w for f in F for e in E)
    L = all(len({w[(f, e)] for e in E}) == len(E) for f in F)
    Rc = all(len({w[(f, e)] for f in F}) == len(F) for e in E)
    return full, L, Rc


def window(pat, f, positions):
    return {pat["w"][(f, e)] for e in positions}


def gadget_checks(pat):
    E, w = pat["E"], pat["w"]
    val = [e for e in E if e not in ("P1", "P2", "P3")]
    ok_xor = ok_ptr = ok_full4 = True
    for g in range(pat["R"]):
        W = [("W1", g), ("W2", g), ("W3", g)]
        V = [window(pat, x, val) for x in W]
        P = [window(pat, x, ["P1", "P2", "P3"]) for x in W]
        ok_xor &= (V[0] ^ V[1] ^ V[2]) == {"x0"}
        ok_ptr &= P[0] == P[1] == P[2]
        A = [window(pat, x, E) for x in W]
        ok_full4 &= len(A[0] ^ A[1] ^ A[2]) == 4
    readers_o = [f for f in pat["F"] if any(pat["w"][(f, e)] == "x0" for e in E)]
    return ok_xor, ok_ptr, ok_full4, len(readers_o)


# ---------------------------------------------------------------- 2. exact H(psi)

def exact_H_psi(k, n):
    t = int(round(log2(k)))
    # j = sum of three uniform t-bit prefixes mod k: convolve
    pj = np.zeros(k)
    for a, b, c in itertools.product(range(k), repeat=3):
        pj[(a + b + c) % k] += 1.0 / k ** 3
    # given j, the output bit is the parity of n iid uniform bits (coordinate j of each value input)
    par = np.array([1.0, 0.0])
    for _ in range(n):
        par = 0.5 * par + 0.5 * par[::-1]
    joint = np.outer(pj, par).ravel()
    joint = joint[joint > 0]
    return float(-(joint * np.log2(joint)).sum()), t + 1


# ---------------------------------------------------------------- 3. exact conditional entropy by enumeration

def psi_eval(k, t, ptrs, vals):
    j = sum(p & (k - 1) for p in ptrs) % k
    bit = 0
    for v in vals:
        bit ^= (v >> j) & 1
    return j, bit


def exact_residual_enumeration(k, R, n):
    """H(x(o) | y_F) by enumerating every site value; pointer sites carry only their t read bits."""
    pat = gadget_pattern(k, R=R, n=n)
    t = pat["t"]
    E, F, w = pat["E"], pat["F"], pat["w"]
    sites = sorted({w[c] for c in w}, key=str)
    width = {s: (t if isinstance(s, tuple) and s[0] in ("a", "b", "c") else k) for s in sites}
    total_bits = sum(width.values())
    offs, o = {}, 0
    for s in sites:
        offs[s] = o
        o += width[s]
    val = [e for e in E if e not in ("P1", "P2", "P3")]
    Nconf = 1 << total_bits
    assert total_bits <= 26, total_bits
    chunk = 1 << 20
    joint = np.zeros(1 << (k + (t + 1) * len(F)), dtype=np.int64)
    for start in range(0, Nconf, chunk):
        cfg = np.arange(start, min(start + chunk, Nconf), dtype=np.int64)

        def site_val(s):
            return (cfg >> offs[s]) & ((1 << width[s]) - 1)

        key = site_val("x0")
        shift = k
        for f in F:
            j = np.zeros_like(cfg)
            for P in ("P1", "P2", "P3"):
                j = j + site_val(w[(f, P)])
            j = j % k
            bit = np.zeros_like(cfg)
            for e in val:
                bit ^= (site_val(w[(f, e)]) >> j) & 1
            key = key | (j << shift) | (bit << (shift + t))
            shift += t + 1
        joint += np.bincount(key, minlength=joint.size)
    p = joint[joint > 0] / Nconf
    H_joint = float(-(p * np.log2(p)).sum())
    yj = joint.reshape(-1, 1 << k).sum(axis=1)
    q = yj[yj > 0] / Nconf
    H_y = float(-(q * np.log2(q)).sum())
    return H_joint - H_y, k * (1 - 1 / k) ** R, total_bits


# ---------------------------------------------------------------- 4. Monte Carlo decoding on the full instance

def monte_carlo(pat, trials, seed):
    rng = random.Random(seed)
    k, t, E, F, w = pat["k"], pat["t"], pat["E"], pat["F"], pat["w"]
    val = [e for e in E if e not in ("P1", "P2", "P3")]
    sites = sorted({w[c] for c in w}, key=str)
    wrong = 0
    unrevealed = 0
    for _ in range(trials):
        x = {s: rng.getrandbits(k) for s in sites}
        y = {f: psi_eval(k, t, [x[w[(f, P)]] for P in ("P1", "P2", "P3")], [x[w[(f, e)]] for e in val]) for f in F}
        revealed = set()
        for g in range(pat["R"]):
            js = {y[("W%d" % i, g)][0] for i in (1, 2, 3)}
            assert len(js) == 1
            j = js.pop()
            b = y[("W1", g)][1] ^ y[("W2", g)][1] ^ y[("W3", g)][1]
            if b != (x["x0"] >> j) & 1:
                wrong += 1
            revealed.add(j)
        unrevealed += k - len(revealed)
    return wrong, unrevealed / trials


# ---------------------------------------------------------------- 5. Evans embedding and loop isotope

def bipartite_edge_coloring(nL, nR, edges, ncol):
    """Konig: proper edge coloring of a bipartite simple graph with max degree <= ncol."""
    nv = nL + nR
    at = [[-1] * ncol for _ in range(nv)]  # at[v][c] = neighbour along colour c
    for (u, v0) in edges:
        U, V = u, nL + v0
        a = next(c for c in range(ncol) if at[U][c] == -1)
        b = next(c for c in range(ncol) if at[V][c] == -1)
        if at[V][a] != -1:
            # swap colours a/b on the alternating path starting at V along colour a
            path = [V]
            cur, col = V, a
            while at[cur][col] != -1:
                nxt = at[cur][col]
                path.append(nxt)
                cur = nxt
                col = b if col == a else a
            # recolour path edges: edges alternate a, b, a, ...
            cols = []
            for i in range(len(path) - 1):
                cols.append(a if i % 2 == 0 else b)
            for i in range(len(path) - 1):
                p, q_, c = path[i], path[i + 1], cols[i]
                at[p][c] = -1
                at[q_][c] = -1
            for i in range(len(path) - 1):
                p, q_, c = path[i], path[i + 1], cols[i]
                nc = b if c == a else a
                at[p][nc] = q_
                at[q_][nc] = p
            assert at[U][a] == -1 and at[V][a] == -1
        at[U][a] = V
        at[V][a] = U
    colouring = {}
    for u in range(nL):
        for c in range(ncol):
            if at[u][c] != -1:
                colouring[(u, at[u][c] - nL)] = c
    return colouring


def evans_embed(N, cells):
    """cells: dict (r, c) -> s with r, c, s in range(N), a partial Latin square. Returns a Latin square of order 2N."""
    M = 2 * N
    A = [[-1] * M for _ in range(M)]
    for (r, c), s in cells.items():
        A[r][c] = s
    # step 1: greedy fill of the N x N block with symbols in range(2N)
    rowset = [set(A[r][c] for c in range(N) if A[r][c] >= 0) for r in range(N)]
    colset = [set(A[r][c] for r in range(N) if A[r][c] >= 0) for c in range(N)]
    for r in range(N):
        for c in range(N):
            if A[r][c] < 0:
                s = next(s for s in range(M) if s not in rowset[r] and s not in colset[c])
                A[r][c] = s
                rowset[r].add(s)
                colset[c].add(s)
    # step 2: rows x missing symbols, N colours -> columns N..2N-1
    edges = [(r, s) for r in range(N) for s in range(M) if s not in rowset[r]]
    col = bipartite_edge_coloring(N, M, edges, N)
    for (r, s), c in col.items():
        A[r][N + c] = s
    # step 3: columns x missing symbols (N-regular), N colours -> rows N..2N-1
    colsets = [set(A[r][c] for r in range(N)) for c in range(M)]
    edges = [(c, s) for c in range(M) for s in range(M) if s not in colsets[c]]
    col = bipartite_edge_coloring(M, M, edges, N)
    for (c, s), rr in col.items():
        A[N + rr][c] = s
    return A


def is_latin(A):
    M = len(A)
    return all(sorted(row) == list(range(M)) for row in A) and all(
        sorted(A[r][c] for r in range(M)) == list(range(M)) for c in range(M))


def loop_realization(pat):
    E, F, w = pat["E"], pat["F"], pat["w"]
    sites = ["x0"] + sorted({w[c] for c in w} - {"x0"}, key=str)
    sidx = {s: i for i, s in enumerate(sites)}
    N = max(len(F), len(E), len(sites))
    cells = {(F.index(f), E.index(e)): sidx[w[(f, e)]] for f in F for e in E}
    A = evans_embed(N, cells)
    M = 2 * N
    latin = is_latin(A)
    embeds = all(A[r][c] == s for (r, c), s in cells.items())
    # quasigroup x.y = A[x][y]; divisions
    rdiv = [[0] * M for _ in range(M)]  # rdiv[x][v] = z with z.v = x
    ldiv = [[0] * M for _ in range(M)]  # ldiv[u][y] = z with u.z = y
    for z in range(M):
        for v in range(M):
            rdiv[A[z][v]][v] = z
            ldiv[z][A[z][v]] = v
    o = sidx["x0"]
    u = 0
    v = ldiv[u][o]
    L = [[A[rdiv[x][v]][ldiv[u][y]] for y in range(M)] for x in range(M)]
    loop_latin = is_latin(L)
    identity = all(L[o][y] == y and L[y][o] == y for y in range(M))
    rows = [A[F.index(f)][v] for f in F]      # f -> f . v
    cols = [A[u][E.index(e)] for e in E]      # e -> u . e
    incid = all(L[rows[i]][cols[j]] == cells[(i, j)] for i in range(len(F)) for j in range(len(E)))
    distinct = len(set(rows)) == len(F) and len(set(cols)) == len(E)
    # the loop is not a group: count associativity failures on a sample and check quadrangle closure on the pattern
    rng = random.Random(7)
    nonassoc = sum(1 for _ in range(2000)
                   for x, y, z in [(rng.randrange(M), rng.randrange(M), rng.randrange(M))]
                   if L[L[x][y]][z] != L[x][L[y][z]])
    return dict(order=M, latin=latin, embeds=embeds, loop_latin=loop_latin, o_is_identity=identity,
                incidence_preserved=incid, labels_distinct=distinct, nonassociative_triples_in_2000=nonassoc)


# ---------------------------------------------------------------- 6. quadrangle closure and the mod-3 count

def shift_relations(F, E, w):
    rel = {}
    for c in F:
        for cp in F:
            if c == cp:
                continue
            S = frozenset((e, ep) for e in E for ep in E if w[(c, e)] == w[(cp, ep)])
            if S:
                rel[(c, cp)] = S
    return rel


def quadrangle_violations(F, E, w):
    """Closure: c e = c'e', c r = c'r', d e = d'e'  =>  d r = d'r'.
    Equivalently the shift relations S_(c,c') = {(e, e') : c e = c' e'} are pairwise disjoint or equal."""
    rel = shift_relations(F, E, w)
    keys = list(rel)
    bad = 0
    example = None
    for i, K1 in enumerate(keys):
        for K2 in keys[i + 1:]:
            S1, S2 = rel[K1], rel[K2]
            if S1 & S2 and S1 != S2:
                bad += 1
                if example is None:
                    ee = next(iter(S1 & S2))
                    rr = next(iter(S1 ^ S2))
                    example = dict(pairs=[str(K1), str(K2)], common=str(ee), differs=str(rr))
    return bad, example


def coherent_shift(w, W, E):
    return any(w[(W[0], u)] == w[(W[1], up)] and w[(W[1], u)] == w[(W[2], up)] and w[(W[2], u)] == w[(W[0], up)]
               for u in E for up in E)


def exhaustive_mod3(nE):
    """All 3 x nE partial Latin rectangles (every cell filled, rows and columns injective), sites up to relabelling.
    Among those with quadrangle closure and a coherent cyclic shift, record |W1 E ^ W2 E ^ W3 E| mod 3."""
    E = list(range(nE))
    W = ["W1", "W2", "W3"]
    cells = [(W[r], e) for r in (1, 2) for e in E]
    stats = dict(patterns=0, closed_coherent=0, closed_coherent_nonzero_mod3=0, coherent_open_sizes=set(),
                 closed_sizes=set())

    def rec(idx, w, nlab):
        if idx == len(cells):
            stats["patterns"] += 1
            coh = coherent_shift(w, W, E)
            size = len(set(w[(W[0], e)] for e in E) ^ set(w[(W[1], e)] for e in E) ^ set(w[(W[2], e)] for e in E))
            bad, _ = quadrangle_violations(W, E, w)
            if coh and bad == 0:
                stats["closed_coherent"] += 1
                stats["closed_sizes"].add(size)
                if size % 3:
                    stats["closed_coherent_nonzero_mod3"] += 1
            elif coh:
                stats["coherent_open_sizes"].add(size)
            return
        f, e = cells[idx]
        r = W.index(f)
        used_row = {w[(f, ee)] for ee in E if (f, ee) in w}
        used_col = {w[(W[rr], e)] for rr in range(r)}
        for s in range(nlab + 1):
            if s in used_row or s in used_col:
                continue
            w[(f, e)] = s
            rec(idx + 1, w, max(nlab, s + 1))
            del w[(f, e)]

    w0 = {("W1", e): e for e in E}
    rec(0, w0, nE)
    stats["coherent_open_sizes"] = sorted(stats["coherent_open_sizes"])
    stats["closed_sizes"] = sorted(stats["closed_sizes"])
    return stats


def random_group_patterns(trials, seed):
    """Group patterns in Z/3 x Z/n: codewords c, c d, c d^2 (d of order 3), random window E.
    They are quadrangle closed by associativity; check |Delta| = 0 mod 3."""
    rng = random.Random(seed)
    nonzero = 0
    sizes = set()
    closed_all = True
    for _ in range(trials):
        nn = rng.randrange(2, 12)
        G = [(a, b) for a in range(3) for b in range(nn)]
        mul = lambda x, y: ((x[0] + y[0]) % 3, (x[1] + y[1]) % nn)
        c = rng.choice(G)
        W = [c, mul(c, (1, 0)), mul(c, (2, 0))]
        E = rng.sample(G, rng.randrange(1, min(len(G), 8) + 1))
        w = {(f, e): mul(f, e) for f in W for e in E}
        bad, _ = quadrangle_violations(W, E, w)
        closed_all &= bad == 0
        size = len(set(w[(W[0], e)] for e in E) ^ set(w[(W[1], e)] for e in E) ^ set(w[(W[2], e)] for e in E))
        sizes.add(size % 3)
        nonzero += size % 3 != 0
    return dict(trials=trials, all_closed=closed_all, nonzero_mod3=nonzero, residues=sorted(sizes))


def main():
    fast = "--fast" in sys.argv
    res = {}
    for k in (4, 8, 16, 32):
        pat = gadget_pattern(k)
        full, L, Rc = check_cancellation(pat)
        xor, ptr, full4, nread = gadget_checks(pat)
        Hpsi, Hpsi_claim = exact_H_psi(k, pat["n"])
        resid = k * (1 - 1 / k) ** pat["R"]
        phi = (Hpsi + resid) / k
        bound = (log2(k) + 1 + 1 / k) / k
        bad, ex = quadrangle_violations(pat["F"][:3], pat["E"], pat["w"])
        res[k] = dict(R=pat["R"], n=pat["n"], F=len(pat["F"]), E=len(pat["E"]),
                      sites=len({pat["w"][c] for c in pat["w"]}), all_cells_filled=full, L=L, R_cancel=Rc,
                      value_xor_is_o=xor, pointer_sets_shared=ptr, full_window_delta_size_4=full4,
                      readers_of_o=nread, H_psi_exact=Hpsi, H_psi_claimed=Hpsi_claim, residual_exact=resid,
                      Phi_exact=phi, Phi_bound_theorem_A=bound, Phi_below_1=phi < 1,
                      quadrangle_violations_in_gadget_0=bad, violation_example=ex)
        print("k=%d" % k, res[k])
    OUT["theorem_A"] = res

    small = {}
    for (k, R, n) in ((2, 1, 3), (2, 2, 3), (2, 3, 3)) + (() if fast else ((4, 1, 3),)):
        try:
            H, formula, bits = exact_residual_enumeration(k, R, n)
        except AssertionError:
            continue
        small["k=%d,R=%d,n=%d" % (k, R, n)] = dict(H_exact=H, formula=formula, enumerated_bits=bits)
        print("exact", k, R, n, H, formula, bits)
    OUT["exact_residual_small_instances"] = small

    mc = {}
    for k, trials in ((4, 4000), (8, 1000)):
        pat = gadget_pattern(k)
        wrong, avg = monte_carlo(pat, trials, seed=k)
        mc[k] = dict(trials=trials, decoding_errors=wrong, mean_unrevealed=avg,
                     formula=k * (1 - 1 / k) ** pat["R"])
        print("mc", k, mc[k])
    OUT["monte_carlo"] = mc

    OUT["loop_realization_k4"] = loop_realization(gadget_pattern(4))
    print("loop", OUT["loop_realization_k4"])

    ex = {}
    for nE in (1, 2, 3, 4):
        ex[nE] = exhaustive_mod3(nE)
        print("exhaustive", nE, ex[nE])
    OUT["theorem_C_prime_exhaustive"] = ex
    OUT["theorem_C_prime_group_samples"] = random_group_patterns(3000, seed=11)
    print("groups", OUT["theorem_C_prime_group_samples"])

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "verify_gadget.json")
    with open(path, "w") as fh:
        json.dump(OUT, fh, indent=1, default=str)
    print("wrote", path)


if __name__ == "__main__":
    main()
