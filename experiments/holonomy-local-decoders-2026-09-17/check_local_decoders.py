#!/usr/bin/env python3
"""Sanity check of Theorem A of
research/artifacts/holonomy-quadrangle-local-decoder-uniqueness-2026-09-17.md
(claim holonomy-quadrangle-patterns-have-unique-local-decoders).

Theorem A: on a pattern with (L), (R), (Q), (H) and split E = U + V, for every value functional T and
every site o, at most one gadget (pointer-equivalence class of rows) has a local decoder
sum_c sigma_c sum_{e in V} T_e [c e] = [o]; that decoder is unique; and supp T lies in one component
of the value graph Gamma.

Sections:
  1. Negative control: the small rotation gadget (k=2, R=3, L=n=13, shifts 1,3,4) of
     quadrangle-closed-patterns-do-not-force-domination: (L)(R)(Q) hold, (H) fails, and o has local
     decoders in all 3 gadgets (T = all ones, q = 2). Teeth: the rotation family over
     R in {2,3,4}, n in {5..13}, L in {5,7,11,13}, shift permutations; every (L)(R)(Q) member with a
     multi-gadget decoded site must fail (H).
  2. Random patterns: gadgets seeded either as Z/L translation gadgets with per-gadget twists of the
     pointer and value positions, or with all value sites distinct; then random merges of value
     sites. Track "H": merges accepted only if (L)(R)(Q)(H) hold. Track "Q": merges accepted if
     (L)(R)(Q) hold. On every final pattern enumerate all local decoders over F_q for every T.
     Prediction: in track H no site has decoders in two gadgets, decoders are unique, supp T sits
     in one Gamma-component; in track Q every multi-gadget site occurs on a pattern failing (H).
Deterministic seeds. Writes check_local_decoders.json next to this file.
"""
import itertools
import json
import os
import random
import time

OUT = {}


# ---------------------------------------------------------------- pattern axioms
def check_L(w):
    return all(len(set(row)) == len(row) for row in w)


def check_R(w):
    nE = len(w[0])
    return all(len({w[c][e] for c in range(len(w))}) == len(w) for e in range(nE))


def classes(w):
    """R(c,c') for c != c' as frozensets of pairs (nonempty only)."""
    nF, nE = len(w), len(w[0])
    pos = [{s: e for e, s in enumerate(row)} for row in w]
    out = {}
    for c in range(nF):
        for d in range(nF):
            if c == d:
                continue
            pairs = frozenset((e, pos[d][s]) for e, s in enumerate(w[c]) if s in pos[d])
            if pairs:
                out[(c, d)] = pairs
    return out


def check_Q(cls):
    seen = {}
    for pairs in cls.values():
        for pr in pairs:
            if pr in seen and seen[pr] != pairs:
                return False
            seen[pr] = pairs
    return True


def check_H(cls, nE):
    """(H) fails iff some word W has W(e) = e and W(y) != y. Union-find on position pairs."""
    parent = list(range(nE * nE))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for pairs in set(cls.values()):
        mp = dict(pairs)
        dom = list(mp)
        for a in dom:
            for b in dom:
                if a != b:
                    ra, rb = find(a * nE + b), find(mp[a] * nE + mp[b])
                    if ra != rb:
                        parent[ra] = rb
    comp = {}
    for a in range(nE):
        for b in range(nE):
            if a == b:
                continue
            r = find(a * nE + b)
            if (r, a) in comp and comp[(r, a)] != b:
                return False
            comp[(r, a)] = b
    return True


def gadgets(w, U):
    g = {}
    for c, row in enumerate(w):
        g.setdefault(frozenset(row[e] for e in U), []).append(c)
    return list(g.values())


def gamma_components(w, U, V, gads, cls):
    parent = {v: v for v in V}

    def find(a):
        while parent[a] != a:
            a = parent[a]
        return a

    for rho in gads:
        for c in rho:
            for d in rho:
                if c != d and (c, d) in cls:
                    for (e, f) in cls[(c, d)]:
                        if e in parent and f in parent:
                            ra, rb = find(e), find(f)
                            if ra != rb:
                                parent[ra] = rb
    return {v: find(v) for v in V}


# ---------------------------------------------------------------- local decoders
def local_decoders(w, rho, V, T, q):
    """All normalized sigma on rho with sum_c sigma_c sum_e T_e [c e] = lambda [o], lambda != 0."""
    cols = []
    for c in rho:
        col = {}
        for e, t in zip(V, T):
            if t:
                s = w[c][e]
                col[s] = (col.get(s, 0) + t) % q
        cols.append(col)
    found = {}
    for sig in itertools.product(range(q), repeat=len(rho)):
        if not any(sig):
            continue
        tot = {}
        for sc, col in zip(sig, cols):
            if sc:
                for s, t in col.items():
                    tot[s] = (tot.get(s, 0) + sc * t) % q
        nz = [(s, v) for s, v in tot.items() if v]
        if len(nz) == 1:
            s, lam = nz[0]
            inv = pow(lam, q - 2, q)
            norm = tuple((x * inv) % q for x in sig)
            found.setdefault(s, set()).add(norm)
    return found


def functionals(rng, q, nV, n_random=150, max_small=2):
    """All normalized T with |supp T| <= max_small, plus n_random random normalized T."""
    Ts = set()
    for k in range(1, max_small + 1):
        for supp in itertools.combinations(range(nV), k):
            for vals in itertools.product(range(1, q), repeat=k - 1):
                T = [0] * nV
                T[supp[0]] = 1
                for i, v in zip(supp[1:], vals):
                    T[i] = v
                Ts.add(tuple(T))
    for _ in range(n_random):
        T = [rng.randrange(q) for _ in range(nV)]
        nz = [i for i, t in enumerate(T) if t]
        if nz:
            inv = pow(T[nz[0]], q - 2, q)
            Ts.add(tuple((t * inv) % q for t in T))
    return sorted(Ts)


def analyse(w, U, V, q, Ts):
    cls = classes(w)
    gads = gadgets(w, U)
    comp = gamma_components(w, U, V, gads, cls)
    res = {"multi_gadget_sites": 0, "nonunique": 0, "T_two_components": 0, "decoder_instances": 0,
           "nontrivial_instances": 0, "max_rows_in_decoder": 0}
    for T in Ts:
        nzT = [i for i, t in enumerate(T) if t]
        per_site = {}
        for gi, rho in enumerate(gads):
            for s, sigs in local_decoders(w, rho, V, T, q).items():
                per_site.setdefault(s, []).append(gi)
                res["decoder_instances"] += 1
                if len(sigs) > 1:
                    res["nonunique"] += 1
                if len({comp[V[i]] for i in nzT}) > 1:
                    res["T_two_components"] += 1
                sz = max(sum(1 for x in sg if x) for sg in sigs)
                res["max_rows_in_decoder"] = max(res["max_rows_in_decoder"], sz)
                if sz >= 2 and len(nzT) >= 2:
                    res["nontrivial_instances"] += 1
        res["multi_gadget_sites"] += sum(1 for g in per_site.values() if len(g) >= 2)
    return res


# ---------------------------------------------------------------- 1. rotation gadget control
def rotation_gadget(R=3, L=13, n=13, shifts=(1, 3, 4)):
    m = (n - 1) // 2
    U = list(range(L))
    V = [L + x for x in range(n)]
    names = {}

    def sid(name):
        return names.setdefault(name, len(names))

    w = []
    for rho in range(R):
        a, c, z = shifts[rho], rho + 1, rho * (R + 1)
        s = {i: (z + (2 * i - 1) * c) % n for i in range(1, m + 1)}
        t = {i: (z + 2 * i * c) % n for i in range(1, m + 1)}
        rows = [dict(), dict(), dict()]
        for i in range(3):
            for y in range(L):
                rows[i][y] = sid(("p", rho, (y + i * a) % L))
        for i in range(1, m + 1):
            rows[0][L + s[i]] = sid(("A", rho, i))
            rows[1][L + s[i]] = sid(("B", rho, i))
            rows[1][L + t[i]] = sid(("A", rho, i))
            rows[2][L + t[i]] = sid(("B", rho, i))
            if i < m:
                rows[0][L + t[i]] = sid(("C", rho, i))
                rows[2][L + s[i + 1]] = sid(("C", rho, i))
        rows[0][L + t[m]] = sid(("D", rho))
        rows[2][L + z] = sid(("D", rho))
        rows[0][L + z] = sid(("Ep", rho))
        rows[2][L + s[1]] = sid(("Ep", rho))
        rows[1][L + z] = sid("o")
        for r in rows:
            assert len(r) == L + n
            w.append([r[e] for e in range(L + n)])
    return w, U, V, names["o"]


def control():
    w, U, V, o = rotation_gadget()
    cls = classes(w)
    gads = gadgets(w, U)
    T = tuple([1] * len(V))
    dec = [sorted(local_decoders(w, rho, V, T, 2).get(o, set())) for rho in gads]
    return {"L": check_L(w), "R": check_R(w), "Q": check_Q(cls), "H": check_H(cls, len(w[0])),
            "gadgets": len(gads), "gadgets_decoding_o": sum(1 for d in dec if d),
            "decoders_of_o": [[list(s) for s in d] for d in dec]}


def rotation_family():
    """Teeth: rotation gadgets over a grid of parameters. Every member with (L)(R)(Q) and a site
    decoded by >= 2 gadgets must fail (H) (Theorem A); check_H must detect each one."""
    stats = {"built": 0, "LRQ_ok": 0, "LRQ_ok_multi_gadget": 0, "LRQ_ok_multi_gadget_H_ok": 0,
             "max_gadgets_decoding_o": 0}
    for R in (2, 3, 4):
        for n in (5, 7, 9, 11, 13):
            for L in (5, 7, 11, 13):
                for shifts in itertools.permutations((1, 2, 3, 4), R):
                    try:
                        w, U, V, o = rotation_gadget(R, L, n, shifts)
                    except (AssertionError, KeyError):
                        continue
                    stats["built"] += 1
                    cls = classes(w)
                    if not (check_L(w) and check_R(w) and check_Q(cls)):
                        continue
                    stats["LRQ_ok"] += 1
                    T = tuple([1] * len(V))
                    k = sum(1 for rho in gadgets(w, U) if o in local_decoders(w, rho, V, T, 2))
                    stats["max_gadgets_decoding_o"] = max(stats["max_gadgets_decoding_o"], k)
                    if k >= 2:
                        stats["LRQ_ok_multi_gadget"] += 1
                        stats["LRQ_ok_multi_gadget_H_ok"] += int(check_H(cls, len(w[0])))
    return stats


# ---------------------------------------------------------------- 2. random patterns
def seed_pattern(rng, q, L, ncol, G, r, structured, need_H):
    """Twisted translation gadgets; rejection until (L)(R)(Q) (and (H) if need_H) hold."""
    for attempt in range(60):
        mode = "canonical" if attempt == 59 else rng.choice(["random", "translate"])
        w, U, V = _seed(rng, L, ncol, G, r, structured, mode)
        cls = classes(w)
        if check_L(w) and check_R(w) and check_Q(cls) and (not need_H or check_H(cls, len(w[0]))):
            return w, U, V, mode
    raise AssertionError("canonical seed failed")


def _seed(rng, L, ncol, G, r, structured, mode):
    U = list(range(L))
    V = list(range(L, L + L * ncol))
    w, nxt = [], [0]

    def new():
        nxt[0] += 1
        return nxt[0] - 1

    for rho in range(G):
        offs = rng.sample(range(L), r)
        alpha = list(range(L))
        beta = [(x, th) for th in range(ncol) for x in range(L)]
        if mode == "random":
            rng.shuffle(alpha)
            rng.shuffle(beta)
        elif mode == "translate":
            shift = [rng.randrange(L) for _ in range(ncol)]
            perm = list(range(ncol))
            rng.shuffle(perm)
            beta = [((x + shift[th]) % L, perm[th]) for th in range(ncol) for x in range(L)]
        psite = {y: new() for y in range(L)}
        vsite = {(x, th): new() for x in range(L) for th in range(ncol)}
        for g in offs:
            row = [psite[(alpha[y] + g) % L] for y in U]
            for i, e in enumerate(V):
                x, th = beta[i]
                row.append(vsite[((x - g) % L, th)] if structured else new())
            w.append(row)
    return w, U, V


def random_merges(rng, w, U, V, attempts, need_H):
    nE = len(w[0])
    for _ in range(attempts):
        vs = sorted({w[c][e] for c in range(len(w)) for e in V})
        if len(vs) < 2:
            break
        s, t = rng.sample(vs, 2)
        w2 = [[s if x == t else x for x in row] for row in w]
        if not (check_L(w2) and check_R(w2)):
            continue
        cls = classes(w2)
        if not check_Q(cls):
            continue
        if need_H and not check_H(cls, nE):
            continue
        w = w2
    return w


def glue_attempts(rng, w, U, V, q, Ts, n_T):
    """Merge a site decoded by one gadget into a different site decoded by another gadget (same T).
    Both gadgets then decode the merged site. Theorem A predicts (L)(R)(Q) + (H) never all hold."""
    gads = gadgets(w, U)
    stats = {"tried": 0, "LRQ_ok": 0, "LRQ_ok_H_ok": 0, "LRQ_ok_multi_confirmed": 0}
    for T in rng.sample(Ts, min(n_T, len(Ts))):
        dec = [local_decoders(w, rho, V, T, q) for rho in gads]
        pairs = [(s, t) for i in range(len(gads)) for j in range(len(gads)) if i < j
                 for s in dec[i] for t in dec[j] if s != t]
        if not pairs:
            continue
        s, t = rng.choice(pairs)
        stats["tried"] += 1
        w2 = [[s if x == t else x for x in row] for row in w]
        if not check_L(w2):
            stats["fail_L"] = stats.get("fail_L", 0) + 1
            continue
        if not check_R(w2):
            stats["fail_R"] = stats.get("fail_R", 0) + 1
            continue
        cls = classes(w2)
        if not check_Q(cls):
            stats["fail_Q"] = stats.get("fail_Q", 0) + 1
            continue
        stats["LRQ_ok"] += 1
        stats["LRQ_ok_H_ok"] += int(check_H(cls, len(w2[0])))
        g2 = gadgets(w2, U)
        stats["LRQ_ok_multi_confirmed"] += int(
            sum(1 for rho in g2 if s in local_decoders(w2, rho, V, T, q)) >= 2)
    return stats


CONFIGS = [
    # q, L = |U|, ncol, G gadgets, r rows per gadget; |V| = L * ncol
    (2, 4, 2, 2, 3),
    (2, 4, 3, 3, 2),
    (3, 3, 2, 2, 2),
    (2, 5, 2, 2, 3),
    (3, 4, 2, 2, 3),
    (2, 3, 3, 3, 2),
]


def random_track(need_H, n_patterns, attempts, seed):
    rng = random.Random(seed)
    agg = {"patterns": 0, "patterns_H_ok": 0, "functionals_tested": 0, "multi_gadget_sites": 0,
           "multi_gadget_patterns": 0, "multi_gadget_patterns_failing_H": 0, "nonunique_on_H_ok": 0,
           "T_two_components_on_H_ok": 0, "decoder_instances": 0, "nontrivial_instances": 0,
           "max_rows_in_decoder": 0, "max_gadgets": 0, "seed_modes": {},
           "glue": {"tried": 0, "LRQ_ok": 0, "LRQ_ok_H_ok": 0, "LRQ_ok_multi_confirmed": 0}}
    for i in range(n_patterns):
        q, L, ncol, G, r = CONFIGS[i % len(CONFIGS)]
        w, U, V, mode = seed_pattern(rng, q, L, ncol, G, r, (i % 3 != 2), need_H)
        agg["seed_modes"][mode] = agg["seed_modes"].get(mode, 0) + 1
        w = random_merges(rng, w, U, V, attempts, need_H)
        cls = classes(w)
        assert check_L(w) and check_R(w) and check_Q(cls)
        hok = check_H(cls, len(w[0]))
        assert hok or not need_H
        Ts = functionals(rng, q, len(V))
        res = analyse(w, U, V, q, Ts)
        agg["functionals_tested"] += len(Ts)
        agg["patterns"] += 1
        agg["patterns_H_ok"] += int(hok)
        agg["max_gadgets"] = max(agg["max_gadgets"], len(gadgets(w, U)))
        agg["multi_gadget_sites"] += res["multi_gadget_sites"]
        agg["decoder_instances"] += res["decoder_instances"]
        agg["nontrivial_instances"] += res["nontrivial_instances"]
        if hok:
            agg["nonunique_on_H_ok"] += res["nonunique"]
            agg["T_two_components_on_H_ok"] += res["T_two_components"]
        agg["max_rows_in_decoder"] = max(agg["max_rows_in_decoder"], res["max_rows_in_decoder"])
        if res["multi_gadget_sites"]:
            agg["multi_gadget_patterns"] += 1
            agg["multi_gadget_patterns_failing_H"] += int(not hok)
        if hok:
            for k, v in glue_attempts(rng, w, U, V, q, Ts, 12).items():
                agg["glue"][k] = agg["glue"].get(k, 0) + v
    return agg


def main():
    t0 = time.time()
    OUT["control_rotation_gadget"] = control()
    c = OUT["control_rotation_gadget"]
    assert c["L"] and c["R"] and c["Q"] and not c["H"] and c["gadgets_decoding_o"] == 3
    OUT["rotation_family"] = rotation_family()
    OUT["configs"] = [dict(zip(("q", "L", "ncol", "G", "r"), cf)) for cf in CONFIGS]
    n_pat = int(os.environ.get("N_PATTERNS", "300"))
    OUT["track_H"] = random_track(True, n_pat, 40, 20260917)
    OUT["track_Q"] = random_track(False, n_pat, 40, 20260918)
    h, qq = OUT["track_H"], OUT["track_Q"]
    OUT["prediction_holds"] = (
        h["multi_gadget_sites"] == 0 and h["nonunique_on_H_ok"] == 0 and h["T_two_components_on_H_ok"] == 0
        and qq["nonunique_on_H_ok"] == 0 and qq["T_two_components_on_H_ok"] == 0
        and qq["multi_gadget_patterns"] == qq["multi_gadget_patterns_failing_H"]
        and OUT["rotation_family"]["LRQ_ok_multi_gadget_H_ok"] == 0
        and h["glue"]["LRQ_ok_H_ok"] == 0 and qq["glue"]["LRQ_ok_H_ok"] == 0
        and h["glue"]["LRQ_ok_multi_confirmed"] == h["glue"]["LRQ_ok"]
        and qq["glue"]["LRQ_ok_multi_confirmed"] == qq["glue"]["LRQ_ok"])
    OUT["seconds"] = round(time.time() - t0, 1)
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_local_decoders.json")
    with open(path, "w") as f:
        json.dump(OUT, f, indent=1)
    print(json.dumps({k: v for k, v in OUT.items() if k != "configs"}, indent=1))


if __name__ == "__main__":
    main()


