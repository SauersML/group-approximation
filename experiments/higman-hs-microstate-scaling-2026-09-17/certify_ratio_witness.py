#!/usr/bin/env python3
"""Exact rational certificates for the six-dimensional HS word-ratio witnesses.

  H4 (Higman four-cycle):   e_(g_0) > 38 * sum_j e_(r_j)   at an exact U(6) tuple
  H3 (trivial three-cycle): e_(g_0) > 10 * sum_j e_(r_j)   at an exact U(6) tuple

Default mode replays the committed JSON witnesses from their integer Cayley
parameters only (Q(i) arithmetic from experiments/hs_word_certificate.py, no
floating point) and checks that the committed matrices agree.
`--derive` (needs numpy + the .npz optimizer outputs in this directory) rounds
the floating-point optimizers to denominator 1024 and rewrites the witnesses.
"""
import argparse, json, sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "experiments"))
from hs_word_certificate import cayley, check, encode_matrix  # noqa: E402

DEN = 1024
CASES = {
    "cycle4": dict(npz="many_cycle4_d6.npz", k=4, d=6, coefficient="38",
                   relators=[[1, 2, -1, -2, -2], [2, 3, -2, -3, -3],
                             [3, 4, -3, -4, -4], [4, 1, -4, -1, -1]]),
    "cycle3": dict(npz="many_cycle3_d6.npz", k=3, d=6, coefficient="10",
                   relators=[[1, 2, -1, -2, -2], [2, 3, -2, -3, -3],
                             [3, 1, -3, -1, -1]]),
}


def candidate(case):
    c = CASES[case]
    return {"generators": ["a", "b", "c", "d"][:c["k"]], "relators": c["relators"],
            "word": [1], "coefficient": c["coefficient"]}


def witness_path(case):
    return HERE / f"ratio_witness_{case}_d6.json"


def derive(case):
    import numpy as np
    c = CASES[case]
    z = np.load(HERE / c["npz"])
    d = c["d"]
    rows = []
    for i in range(c["k"]):
        u = z["arr_%d" % i]
        K = (np.eye(d) - u) @ np.linalg.inv(np.eye(d) + u)    # U = (I-K)(I+K)^{-1}
        par = [K[j, j].imag for j in range(d)]
        for a in range(d):
            for b in range(a + 1, d):
                par += [K[a, b].real, K[a, b].imag]
        rows.append([int(round(DEN * p)) for p in par])
    return rows


def build(case, rows):
    c = CASES[case]
    mats = [cayley([Q(n, DEN) for n in row], c["d"]) for row in rows]
    res = check(candidate(case), mats)
    if res["status"] != "counterexample":
        raise ValueError(f"{case}: rounded tuple is not a strict counterexample: {res}")
    return {"format": "hs-word-counterexample-v1", "candidate": candidate(case),
            "construction": {"type": "rational-skew-hermitian-cayley", "denominator": DEN,
                             "integer_parameters": rows},
            "matrices": [encode_matrix(a) for a in mats], "verification": res}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--derive", action="store_true")
    ap.add_argument("cases", nargs="*", default=list(CASES))
    a = ap.parse_args()
    for case in a.cases:
        if a.derive:
            rows = derive(case)
        else:
            rows = json.loads(witness_path(case).read_text())["construction"]["integer_parameters"]
        w = build(case, rows)
        rendered = json.dumps(w, indent=1) + "\n"
        if a.derive:
            witness_path(case).write_text(rendered)
        elif witness_path(case).read_text() != rendered:
            sys.exit(f"{case}: committed witness differs from exact reconstruction")
        v = w["verification"]
        ratio = Q(v["word_energy"]) / Q(v["relator_energy_sum"])
        print(f"PASS {case}: exact U(6) tuple, e_a/sum e_r = {float(ratio):.6f} > {CASES[case]['coefficient']}, "
              f"margin {float(Q(v['strict_margin'])):.3e}")


if __name__ == "__main__":
    main()
