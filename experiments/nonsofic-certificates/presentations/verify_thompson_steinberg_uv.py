#!/usr/bin/env python3
"""Three generators: Bleak--Quick's two-generator V (Theorem 1.3) plus the leaf transvection x.

u = t_(00,01) t_(10,110) t_(10,111) and v = (01 10 11), maps on the right, sent to L^x by
psi(g) = U_g^-1.  x = 1 + S[00]T[01].  The x-relators are those of
verify_thompson_steinberg_presentation.py with every conjugator a word in u, v:
configuration conjugators by BFS; swaps (alpha beta) as conjugates of u^3 = (00 01); and the
centralizer generators iota_1(u) = (100 101)(110 1110)(110 1111), iota_1(v) = (101 110 111).
The latter two are assembled from swaps, so no deep search is needed.
"""
import hashlib
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify_thompson_steinberg_presentation as TS  # noqa: E402

Lv = TS.Lv
UV_WORDS = [  # Bleak--Quick, arXiv:1511.02123v2, Theorem 1.3, verbatim from the TeX source
    "u^6", "v^3", "(u^{3}v)^4",
    "v^{-1}u(u^{2}v^{-1})^{2}u^{3}vu^{-1}v^{-1}u^{3}vu(uvu^{2}(uv^{-1}u^{3}v)^{3})^{2}uv^{-1}u^{3}v^{-1}",
    "uv^{-1}u^{3}v^{-1}u^{-2}v^{-1}uvu^{2}v^{-1}u^{-1}vu^{2}v^{-1}uvu^{-1}(u^{-1}v^{-1})^{2}u^{3}vu^{-1}",
    "v(uv^{-1}u^{3}v^{-1})^{2}u^{-1}v^{-1}u^{3}v^{-1}u^{-1}v^{-1}u^{3}v",
    "uvu^{3}vuv^{-1}u^{-2}v^{-1}u(u^{2}v)^{2}(u^{2}v^{-1})^{2}u^{3}vu^{-2}v^{-1}u^{3}v",
]
SWAP = [("00", "10"), ("01", "110"), ("00", "00"), ("01", "10")]


def norm(s):
    return re.sub(r"\^(-?\d+)", r"^{\1}", s)


def bfs(units, steps, targets, max_depth, cap):
    found, frontier, seen = {}, [([], Lv.IDENTITY)], {Lv.IDENTITY.key}
    for depth in range(max_depth + 1):
        for w, g in frontier:
            for name, pred in targets.items():
                if name not in found and pred(g):
                    found[name] = w
        if len(found) == len(targets) or depth == max_depth:
            break
        nxt = []
        for w, g in frontier:
            for s, e in steps:
                if w and w[-1] == (s, -e):
                    continue
                ng = g * (units[s] if e == 1 else units[s].inverse())
                if ng.key not in seen and len(seen) < cap:
                    seen.add(ng.key)
                    nxt.append((w + [(s, e)], ng))
        frontier = nxt
    return found, len(seen)


def main():
    t0 = time.time()
    cu, mc, R = TS.cycle_unit, TS.maps_cones, TS.reduce
    out = {}
    units = {"u": cu([["00", "01"]]) * cu([["10", "110"]]) * cu([["10", "111"]]),
             "v": cu([["11", "10", "01"]]), "x": TS.transvection("00", "01")}
    rels_v = [TS.parse_tex(norm(r)) for r in UV_WORDS]
    Lv.set_dual(True)
    out["theorem_1.3_relators_hold"] = [TS.evaluate(r, units).is_identity() for r in rels_v]
    out["u^3 = (00 01)"] = (units["u"] ** 3) == cu([["00", "01"]])
    cfg = {
        "T(10,110)": [("00", "10"), ("01", "110")], "T(00,10)": [("00", "00"), ("01", "10")],
        "T(10,01)": [("00", "10"), ("01", "01")], "T(01,10)": [("00", "01"), ("01", "10")],
        "T(000,010)": [("00", "000"), ("01", "010")], "T(001,011)": [("00", "001"), ("01", "011")],
        "(100 101)": [("00", "100"), ("01", "101")], "(110 1110)": [("00", "110"), ("01", "1110")],
        "(110 1111)": [("00", "110"), ("01", "1111")],
        "(101 110)": [("00", "101"), ("01", "110")], "(101 111)": [("00", "101"), ("01", "111")],
    }
    targets = {k: (lambda pairs: (lambda g: mc(g, pairs)))(p) for k, p in cfg.items()}
    Lv.set_dual(False)
    found, explored = bfs(units, [("u", 1), ("u", -1), ("v", 1), ("v", -1)], targets,
                          int(os.environ.get("BFS_DEPTH", "14")), int(os.environ.get("BFS_CAP", "1500000")))
    out["bfs_explored"] = explored
    out["conjugators"] = {k: TS.render(w) for k, w in found.items()}
    out["missing"] = sorted(set(targets) - set(found))
    if out["missing"]:
        print(json.dumps(out, indent=1))
        return 1
    Lv.set_dual(True)
    U3 = [("u", 1)] * 3
    X = [("x", 1)]

    def conj(name, word):
        g = found[name]
        return R(g + word + TS.inv(g))

    swap = {k: conj(k, U3) for k in ("(100 101)", "(110 1110)", "(110 1111)", "(101 110)", "(101 111)")}
    iota_u = R(swap["(100 101)"] + swap["(110 1110)"] + swap["(110 1111)"])
    iota_v_target = cu([["111", "110", "101"]])
    iota_v = R(swap["(101 110)"] + swap["(101 111)"])
    if TS.evaluate(iota_v, units) != iota_v_target:
        iota_v = R(swap["(101 111)"] + swap["(101 110)"])
    out["exact_images"] = {
        "iota1(u)": TS.evaluate(iota_u, units) == cu([["100", "101"]]) * cu([["110", "1110"]]) * cu([["110", "1111"]]),
        "iota1(v)": TS.evaluate(iota_v, units) == iota_v_target,
    }
    for k in cfg:
        if k.startswith("T("):
            out["exact_images"][k] = TS.evaluate(conj(k, X), units) == TS.transvection(*k[2:-1].split(","))
    rels = [("V", "Bleak-Quick Thm 1.3 r%d" % i, w) for i, w in enumerate(rels_v, 1)]
    rels += [("X", "x^2", X * 2), ("X", "(u^3 x)^3", (U3 + X) * 3),
             ("H", "[x, iota1(u)]", TS.comm(X, iota_u)), ("H", "[x, iota1(v)]", TS.comm(X, iota_v)),
             ("B", "[T(00,01), T(10,110)]", TS.comm(X, conj("T(10,110)", X))),
             ("B", "[T(00,01), T(00,10)]", TS.comm(X, conj("T(00,10)", X))),
             ("B", "[T(00,01), T(10,01)]", TS.comm(X, conj("T(10,01)", X))),
             ("C", "[T(00,01), T(01,10)] = T(00,10)", R(TS.comm(X, conj("T(01,10)", X)) + TS.inv(conj("T(00,10)", X)))),
             ("Q", "T(000,010) T(001,011) = T(00,01)", R(conj("T(000,010)", X) + conj("T(001,011)", X) + TS.inv(X)))]
    fails = [n for _f, n, w in rels if not TS.evaluate(w, units).is_identity()]
    out["relators_failing_in_G"] = fails
    out["relator_count"], out["generator_count"] = len(rels), 3
    out["total_length"] = sum(len(w) for _f, _n, w in rels)
    out["max_length"] = max(len(w) for _f, _n, w in rels)
    out["relators"] = [{"family": f, "name": n, "word": TS.render(w), "length": len(w)} for f, n, w in rels]
    out["relator_sha256"] = hashlib.sha256("\n".join(TS.render(w) for _f, _n, w in rels).encode()).hexdigest()
    neg = {"(v x)^3 = 1": ([("v", 1)] + X) * 3, "[x, u^3] = 1": TS.comm(X, U3),
           "[x, T(01,10)] = 1": TS.comm(X, conj("T(01,10)", X)), "[x, u] = 1": TS.comm(X, [("u", 1)])}
    out["negative_controls_nonidentity"] = {k: not TS.evaluate(w, units).is_identity() for k, w in neg.items()}
    out["dual"] = Lv.dual_stats()
    out["seconds"] = round(time.time() - t0, 1)
    ok = (all(out["theorem_1.3_relators_hold"]) and out["u^3 = (00 01)"] and not fails
          and all(out["exact_images"].values()) and all(out["negative_controls_nonidentity"].values()))
    out["verdict"] = "PASS" if ok else "FAIL"
    with open(os.environ.get("OUT_JSON", os.path.join(HERE, "thompson-steinberg-uv-presentation.json")), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "relators"}, indent=1))
    for f, n, w in rels:
        print("%s | %-36s | %3d | %s" % (f, n, len(w), TS.render(w)))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
