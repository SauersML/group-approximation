#!/usr/bin/env python3
"""Cross-validation of thicken.dfs against thicken.brute, plus fixed examples.

Search space of the random test: seeded random monoid words (not necessarily
freely reduced) on 2 or 3 generators, 1 to 3 relators, total length <= 9, both
variants.  Every case compares the Boolean answers; every positive dfs answer is
re-verified by recomputing the face count of the returned rotation.
"""
import random
import thicken as T

FIXED = [
    # (relators, expected orient-thickenable, reason)
    (["x", "y"], True, "standard presentation, two balls"),
    (["xx"], True, "RP^2 is a spine of punctured RP^3"),
    (["xxx"], True, "pseudo-projective plane = spine of punctured L(3,1)"),
    (["xyXY"], True, "torus x I"),
    (["xyXy"], True, "Klein bottle, twisted I-bundle is orientable"),
    (["xxX"], True, "dunce hat embeds in R^3"),
    (["xYyyY", "yYyYy"], True, "Lackenby StableAC1june26.tex l.855-876 Heegaard diagram of S^3"),
    (["xxyxzyyzz"], False, "link graph contains K_{3,3}"),
]


def link_edges(K):
    ed = []
    for h in range(K.H):
        a = K.alpha[h]
        if h < a:
            ed.append(tuple(sorted([K.vert(h), K.vert(a)])))
    return sorted(ed)


def main():
    bad = 0
    for rels, exp, why in FIXED:
        K = T.Complex(rels)
        ok, wit, nodes = T.dfs(K, "orient")
        okb = T.brute(K, "orient")[0]
        flag = "OK" if (ok == exp == okb) else "MISMATCH"
        bad += flag != "OK"
        print(flag, rels, "orient", ok, "brute", okb, "expected", exp, "--", why)
    K = T.Complex(["xxyxzyyzz"])
    print("link edges of xxyxzyyzz:", link_edges(K))
    rng = random.Random(20260916)
    stats = {"cases": 0, "orient_true": 0, "either_true": 0, "either_not_orient": 0}
    examples_diff = []
    for trial in range(3000):
        n = rng.choice([2, 3])
        gens = "xyz"[:n]
        m = rng.choice([1, 2, 3])
        total = rng.randint(m, 9)
        cuts = sorted(rng.sample(range(1, total), m - 1)) if m > 1 else []
        lens = [b - a for a, b in zip([0] + cuts, cuts + [total])]
        rels = ["".join(rng.choice(gens + gens.upper()) for _ in range(L)) for L in lens]
        K = T.Complex(rels)
        res = {}
        for v in ("orient", "either"):
            ok, wit, nodes = T.dfs(K, v)
            okb = T.brute(K, v)[0]
            if ok != okb:
                bad += 1
                print("MISMATCH", rels, v, ok, okb)
            if ok:
                orders, flips = wit
                F = T.faces(T.sigma_from(K, orders, flips), K.alpha)
                if F != K.F_target:
                    bad += 1
                    print("BAD WITNESS", rels, v, F, K.F_target)
            res[v] = ok
        stats["cases"] += 1
        stats["orient_true"] += res["orient"]
        stats["either_true"] += res["either"]
        if res["either"] and not res["orient"]:
            stats["either_not_orient"] += 1
            if len(examples_diff) < 3:
                examples_diff.append(rels)
    print("random cross-check:", stats, "examples either-but-not-orient:", examples_diff)
    print("TOTAL MISMATCHES", bad)
    return bad


if __name__ == "__main__":
    raise SystemExit(1 if main() else 0)
