#!/usr/bin/env python3
"""Two generators: Tietze-reduce the three-generator presentation <u, v, x | 16 relators>.

w = v . T(alpha, beta) with alpha, beta inside the cone 00. Every Thompson unit of v fixes 00w
pointwise, so v and T commute. Then w^6 = 1, w^4 = v and w^3 = T. With g a word in u, v sending
00 -> alpha and 01 -> beta, x = g^-1 w^3 g. Substituting v -> w^-2 and x -> G^-1 w^(+-3) G
(G = g with v -> w^-2) into the sixteen relators gives <u, w | 16 relators>.
Checks: the needed identities hold exactly; every substituted relator holds in L^x.
"""
import hashlib
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify_thompson_steinberg_presentation as TS  # noqa: E402
import verify_thompson_steinberg_uv as UV  # noqa: E402

Lv = TS.Lv


def parse_rendered(text):
    out = []
    for tok in text.split():
        if tok.endswith("^-1"):
            out.append((tok[:-3], -1))
        else:
            out.append((tok, 1))
    return out


def main():
    t0 = time.time()
    cu = TS.cycle_unit
    src = json.load(open(os.environ.get("UV_JSON", os.path.join(HERE, "thompson-steinberg-uv-presentation.json"))))
    assert src["verdict"] == "PASS"
    rels16 = [(r["name"], parse_rendered(r["word"])) for r in src["relators"]]
    units = {"u": cu([["00", "01"]]) * cu([["10", "110"]]) * cu([["10", "111"]]), "v": cu([["11", "10", "01"]])}
    x_unit = TS.transvection("00", "01")
    choices = [("000", "001"), ("001", "000"), ("0000", "001"), ("000", "0010")]
    targets = {"%s|%s" % c: (lambda c: (lambda g: TS.maps_cones(g, [("00", c[0]), ("01", c[1])])))(c) for c in choices}
    Lv.set_dual(False)
    found, explored = UV.bfs(units, [("u", 1), ("u", -1), ("v", 1), ("v", -1)], targets,
                             int(os.environ.get("BFS_DEPTH", "12")), int(os.environ.get("BFS_CAP", "800000")))
    out = {"bfs_explored": explored, "conjugators": {k: TS.render(w) for k, w in found.items()}}
    Lv.set_dual(True)
    best = None
    for key, g in found.items():
        alpha, beta = key.split("|")
        T = TS.transvection(alpha, beta)
        w_unit = units["v"] * T
        g_sub = []
        for s, e in g:
            g_sub += [("w", -e)] * 2 if s == "v" else [(s, e)]
        G = TS.reduce(g_sub)
        wu = {"u": units["u"], "w": w_unit}
        checks = {
            "[v, T] = 1": (units["v"] * T) == (T * units["v"]),
            "w^6 = 1": (w_unit ** 6).is_identity(),
            "w^-2 = v": w_unit ** -2 == units["v"],
            "G^-1 w^3 G = x": TS.evaluate(TS.inv(G) + [("w", 1)] * 3 + G, wu) == x_unit,
        }
        rels = []
        for name, word in rels16:
            new = []
            for s, e in word:
                if s == "v":
                    new += [("w", -e)] * 2
                elif s == "x":
                    new += TS.inv(G) + [("w", e)] * 3 + G
                else:
                    new.append((s, e))
            if name != "x^2":  # after substitution x^2 is G^-1 w^6 G, a conjugate of r2^-1 = w^6
                rels.append((name, TS.reduce(new)))
        fails = [n for n, w in rels if not TS.evaluate(w, wu).is_identity()]
        total = sum(len(w) for _n, w in rels)
        cand = {"transvection": key, "g": TS.render(g), "checks": checks, "relators_failing_in_G": fails,
                "total_length": total, "max_length": max(len(w) for _n, w in rels),
                "relators": [{"name": n, "word": TS.render(w), "length": len(w)} for n, w in rels]}
        ok = all(checks.values()) and not fails
        if ok and (best is None or total < best["total_length"]):
            best = cand
        out.setdefault("candidates", []).append({k: v for k, v in cand.items() if k != "relators"})
    if best is not None:
        out["chosen"] = best
        out["relator_sha256"] = hashlib.sha256("\n".join(r["word"] for r in best["relators"]).encode()).hexdigest()
        wu = {"u": units["u"], "w": units["v"] * TS.transvection(*best["transvection"].split("|"))}
        neg = {"[u, w] = 1": TS.comm([("u", 1)], [("w", 1)]), "w^3 = 1": [("w", 1)] * 3, "w^2 = 1": [("w", 1)] * 2}
        out["negative_controls_nonidentity"] = {k: not TS.evaluate(w, wu).is_identity() for k, w in neg.items()}
    out["dual"] = Lv.dual_stats()
    out["seconds"] = round(time.time() - t0, 1)
    out["verdict"] = "PASS" if best is not None and all(out["negative_controls_nonidentity"].values()) else "FAIL"
    with open(os.environ.get("OUT_JSON", os.path.join(HERE, "two-generator-presentation.json")), "w") as fh:
        json.dump(out, fh, indent=1)
    summary = {k: v for k, v in out.items() if k != "chosen"}
    if best is not None:
        summary["chosen"] = {k: v for k, v in best.items() if k != "relators"}
        summary["chosen_lengths"] = [(r["name"], r["length"]) for r in best["relators"]]
    print(json.dumps(summary, indent=1))
    return 0 if out["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
