#!/usr/bin/env python3
"""Analyze kernel profiles k_D(a,b) = dim ker (u,v) -> a u + b v on F_2[M_(D,D+3)]^2.

Inputs: prof_small.jsonl (k = 0..7) and out/d8_*.jsonl (k = 8), samples.json.
Checks:
  - consistency with the landed census (eada0577f): every 'solved' pair has some k_D > 0 with D <= 7,
    every 'stubborn' pair has k_D = 0 for D <= 7;
  - monotonicity k_D <= k_(D+1) (right multiplication by x_0 embeds window D into window D+1);
  - S_(2,4) first positive degree against the landed census minimal degrees where known;
Reports for each pair: first positive degree, profile, ratios k_D / |V_D|, and whether the positive part of
the profile satisfies a linear recurrence with integer coefficients of order <= 2 (exact check on the
available terms, needs at least 2*order+1 positive terms to be meaningful).
"""
import glob, json
from fractions import Fraction


def load(files):
    prof = {}
    meta = {}
    for f in files:
        for line in open(f):
            line = line.strip()
            if not line.startswith("{"):
                continue
            d = json.loads(line)
            key = (d["set"], d["a"], d["b"])
            prof.setdefault(key, {})[d["k"]] = d["kernel"]
            meta[(d["set"], d["k"])] = (d["V"], d["rows"])
    return prof, meta


def recurrence(seq, order):
    """Exact test: does seq satisfy s_n = c_1 s_(n-1) + ... + c_r s_(n-r) with rational c on all terms?"""
    if len(seq) < 2 * order + 1:
        return None
    # solve first r equations
    import itertools
    rows = [[Fraction(seq[n - i]) for i in range(1, order + 1)] + [Fraction(seq[n])] for n in range(order, 2 * order)]
    # Gaussian elimination
    m = [r[:] for r in rows]
    for col in range(order):
        piv = next((r for r in range(col, order) if m[r][col] != 0), None)
        if piv is None:
            return None
        m[col], m[piv] = m[piv], m[col]
        for r in range(order):
            if r != col and m[r][col] != 0:
                f = m[r][col] / m[col][col]
                m[r] = [x - f * y for x, y in zip(m[r], m[col])]
    c = [m[i][order] / m[i][i] for i in range(order)]
    ok = all(sum(c[i] * seq[n - 1 - i] for i in range(order)) == seq[n] for n in range(order, len(seq)))
    return [str(x) for x in c] if ok else False


def main():
    samples = json.load(open("samples.json"))
    prof, meta = load(["prof_small.jsonl"] + sorted(glob.glob("out/d8_*.jsonl")))
    role = {}
    for p in samples["stubborn"]:
        role[("S35", p["a"], p["b"])] = "stubborn:" + p["category"]
    for p in samples["solved"]:
        role[("S35", p["a"], p["b"])] = "solved"
    for p in samples["s24"]:
        role[("S24", p["a"], p["b"])] = "s24"
    problems = []
    summary = {"stubborn_settled_at_8": [], "stubborn_zero_through_8": [], "stubborn_missing_8": []}
    out = []
    for key in sorted(prof, key=lambda k: (k[0], role.get(k, ""), k[1], k[2])):
        ks = prof[key]
        D = sorted(ks)
        seq = [ks[d] for d in D]
        first = next((d for d in D if ks[d] > 0), None)
        r = role.get(key, "?")
        mono = all(ks[D[i]] <= ks[D[i + 1]] for i in range(len(D) - 1) if D[i + 1] == D[i] + 1)
        if not mono:
            problems.append(("nonmonotone", key, seq))
        if r == "solved" and not (first is not None and first <= 7):
            problems.append(("solved_pair_not_positive_by_7", key, seq))
        if r.startswith("stubborn") and any(ks.get(d, 0) > 0 for d in range(8)):
            problems.append(("stubborn_pair_positive_by_7", key, seq))
        if r.startswith("stubborn"):
            if 8 not in ks:
                summary["stubborn_missing_8"].append(key[1:])
            elif ks[8] > 0:
                summary["stubborn_settled_at_8"].append((key[1], key[2], ks[8]))
            else:
                summary["stubborn_zero_through_8"].append(key[1:])
        pos = [ks[d] for d in D if first is not None and d >= first]
        rec = {o: recurrence(pos, o) for o in (1, 2)}
        ratios = {d: round(ks[d] / meta[(key[0], d)][0], 6) for d in D}
        out.append({"set": key[0], "a": key[1], "b": key[2], "role": r, "first_positive": first,
                    "profile": dict(zip(D, seq)), "ratio_to_V": ratios, "recurrence_on_positive": rec})
    json.dump({"pairs": out, "problems": problems, "summary": summary,
               "V_rows": {f"{s}:{k}": v for (s, k), v in sorted(meta.items())}}, open("analysis.json", "w"), indent=1)
    print("PROBLEMS", len(problems), problems[:5])
    print("STUBBORN settled_at_8", len(summary["stubborn_settled_at_8"]), "zero_through_8",
          len(summary["stubborn_zero_through_8"]), "missing_8", len(summary["stubborn_missing_8"]))
    for rec in out:
        if rec["role"] in ("solved", "s24") or rec["first_positive"] is not None:
            print(rec["set"], rec["a"], rec["b"], rec["role"], "first", rec["first_positive"], rec["profile"],
                  "rec", rec["recurrence_on_positive"])
    print("DONE")


if __name__ == "__main__":
    main()
