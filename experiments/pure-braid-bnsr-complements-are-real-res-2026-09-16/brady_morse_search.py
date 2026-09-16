#!/usr/bin/env python3
"""Hill-climb the coset correction t: S_n -> R in the Brady-complex Morse test (see brady_morse.py).

Objective: the number of vertex types sigma in S_n whose ascending link carries the pi_1 = 1 certificate (so it is connected
and simply connected), subject to all edge increments being nonzero.  Moves change t[sigma] at a failing type.  Only the
types whose ascending link can change are re-evaluated.  A run that reaches all n! types is a certificate (conditional on
the code) that [chi] lies in Sigma^2(P_n); a run that does not proves nothing.

Usage: timeout 600 python3 brady_morse_search.py [n] [seconds_per_case]   (writes brady_morse_search_n<n>.json)
"""
import itertools, json, os, random, sys, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from brady_morse import (build_dual, build_link, winding2, perm_of, inverse_word, pmul, pinv, components,
                         pi1_certificate, b1_mod)  # noqa: E402


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 60.0
    t0 = time.time()
    NC, lift, c, checks = build_dual(n)
    verts, edges, tris = build_link(n, NC, lift)
    V = len(verts)
    W2, P = [], []
    for sgn, w in verts:
        word = lift[w] if sgn == "+" else inverse_word(lift[w])
        W2.append(winding2(word, n))
        P.append(perm_of(word, n))
    Sn = list(itertools.permutations(range(n)))
    pairs = list(itertools.combinations(range(n), 2))
    # which types see type sigma as a neighbour type: tau * P[y] = sigma
    affected = {s: {s} | {pmul(s, pinv(P[y])) for y in range(V)} for s in Sn}
    rng = random.Random(20260916)

    def status(sg, base, t):
        up = [y for y in range(V) if base[sg][y] + t[pmul(sg, P[y])] - t[sg] > 0]
        S = set(up)
        if not up:
            return False
        es = [e for e in edges if e[0] in S and e[1] in S]
        ncomp, _ = components(up, es)
        if ncomp > 1:
            return False
        ts = [tr for tr in tris if tr[0] in S and tr[1] in S and tr[2] in S]
        return pi1_certificate(up, es, ts)

    def minabs(base, t):
        return min(abs(base[sg][y] + t[pmul(sg, P[y])] - t[sg]) for sg in Sn for y in range(V))

    def zero_sum_char(zero_pairs, scale=1000):
        while True:
            a = {p: rng.randint(-scale, scale) for p in pairs}
            for p in zero_pairs:
                a[p] = 0
            free = [p for p in pairs if p not in zero_pairs]
            a[free[-1]] -= sum(a.values())
            if all(a[p] != 0 for p in free):
                return a

    cases = [("generic zero sum (in Sigma^2 by Theorem M; calibration)", zero_sum_char([])),
             ("zero sum with c_12 = 0 (open case)", zero_sum_char([(0, 1)])),
             ("zero sum with c_123 = 0 (open case)", None)]
    # c_123 = a12 + a13 + a23 = 0
    while True:
        a = zero_sum_char([])
        a[(1, 2)] = -(a[(0, 1)] + a[(0, 2)])
        rest = [p for p in pairs if p not in ((0, 1), (0, 2), (1, 2))]
        a[rest[-1]] -= sum(a.values())
        if all(v != 0 for v in a.values()):
            break
    cases[2] = (cases[2][0], a)
    if n == 5:
        cases.append(("local triple {1,2,3} (control: must fail)", {(0, 1): 1, (0, 2): 1, (1, 2): -2}))
    out = []
    for label, a in cases:
        base = {sg: [sum(val * W2[y][sg[i]][sg[j]] for (i, j), val in a.items()) / 2.0 for y in range(V)] for sg in Sn}
        scale = max(abs(v) for v in a.values())
        t = {sg: rng.uniform(-1e-3, 1e-3) * scale for sg in Sn}
        good = {sg: status(sg, base, t) for sg in Sn}
        score = sum(good.values())
        start_score = score
        tc = time.time()
        moves = accepted = 0
        while score < len(Sn) and time.time() - tc < budget:
            bad = [sg for sg in Sn if not good[sg]]
            sg = rng.choice(bad)
            old = t[sg]
            t[sg] = old + rng.choice([-1, 1]) * rng.choice([0.01, 0.1, 0.5, 1.0, 2.0]) * scale
            moves += 1
            new = {tau: status(tau, base, t) for tau in affected[sg]}
            ns = score - sum(good[tau] for tau in affected[sg]) + sum(new.values())
            if ns >= score:
                good.update(new)
                accepted += ns > score
                score = ns
            else:
                t[sg] = old
        mi = minabs(base, t)
        verdict = "all types certified: criterion passes at level 2" if score == len(Sn) and mi > 1e-9 else \
            f"{score}/{len(Sn)} types certified"
        rec = {"label": label, "a": {f"{i+1}{j+1}": v for (i, j), v in a.items()}, "start_score": start_score,
               "final_score": score, "types": len(Sn), "moves": moves, "improving_moves": accepted,
               "min_abs_increment": mi, "verdict": verdict}
        if score == len(Sn) and mi > 1e-9:
            rec["t"] = {"".join(map(str, sg)): t[sg] for sg in Sn}
        out.append(rec)
        print(label, rec["a"], "->", verdict, f"(start {start_score}, moves {moves}, min|inc| {mi:.3g})",
              f"{time.time()-t0:.1f}s", flush=True)
        with open(os.path.join(HERE, f"brady_morse_search_n{n}.json"), "w") as f:
            json.dump({"n": n, "seed": 20260916, "budget_seconds_per_case": budget, "results": out}, f, indent=1)


if __name__ == "__main__":
    main()
