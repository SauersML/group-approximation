#!/usr/bin/env python3
"""Table of exact cogrowth counts for F (32 terms), the certified consequences of the best
certified norm bound, and an honest trend summary.

Reads epg_certify.py (the embedded coefficients) and epg_certify.json (the certificate).
Writes cogrowth_table.csv next to this script and prints JSON.

Certified consequences (exact integer/rational arithmetic):
  (a) cogrowth rate mu = lim c_n^{1/n} = 16 ||P||^2 > 16 theta.
  (b) Cayley-graph density. For a 4-regular bipartite graph with adjacency norm rho_A = 4||P||,
      every finite S has |dS| >= h|S| where h = inf |dS|/|S|, and Cheeger-Mohar
      h <= sqrt(16 - rho_A^2) (elementary proof in the claim's route node). Average inner degree
      of S is 4 - |dS|/|S|, so sup_S (avg inner degree) = 4 - h >= 4 - 4 sqrt(1 - ||P||^2).
      With ||P|| > r this certifies a density lower bound, which turns out to be FAR weaker
      than the known combinatorial bound 3.50074529 (Prellberg, arXiv:2609.12290).
  (c) Converse direction: any finite S with average inner degree d gives ||P|| >= d/4
      (Rayleigh quotient of the indicator), so density 3.50074529 only gives ||P|| > 0.875186.
"""
import csv, importlib.util, json, math, os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("epg", os.path.join(HERE, "epg_certify.py"))
epg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(epg)
C = epg.EPG


def main():
    cert = json.load(open(os.path.join(HERE, "epg_certify.json")))
    best = cert["certificates"]["N31_epg_full"][0]
    theta = Fraction(best["theta"])
    r = Fraction(best["rho_lower_bound"])
    assert r * r <= theta

    with open(os.path.join(HERE, "cogrowth_table.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["n", "word_length", "c_n_trivial_words", "c_n_over_c_n_minus_1",
                    "c_n_over_16^n", "c_n^(1/n)", "provenance"])
        for n, x in enumerate(C):
            prov = ("computed in repo (out15.json) + EP-G + HHR" if n <= 15 else
                    "EP-G table, agrees with HHR Case 2 table" if n <= 24 else
                    "EP-G table only (arXiv:1706.07571), not recomputed")
            w.writerow([n, 2 * n, x, f"{x / C[n - 1]:.6f}" if n else "",
                        f"{x / 16 ** n:.6e}", f"{x ** (1 / n):.6f}" if n else "", prov])

    # (b) density: 4 - 4 sqrt(1 - r^2) with a certified rational upper bound on the sqrt
    s2 = 1 - r * r                                   # 1 - r^2, exact
    scale = 10 ** 12
    up = math.isqrt(math.ceil(s2 * scale * scale))
    if up * up < s2 * scale * scale:
        up += 1
    sq_up = Fraction(up, scale)
    assert sq_up * sq_up >= s2
    dens_lb = 4 - 4 * sq_up
    # (c) density 3.50074529 -> norm
    prellberg = Fraction(350074529, 10 ** 8)
    ratios = [C[n] / C[n - 1] for n in range(1, len(C))]
    out = {
        "best_certificate": best,
        "rho_lower_bound": str(r), "rho_lower_bound_float": float(r),
        "mu_lower_bound_16theta": float(16 * theta),
        "certified_density_lower_bound_from_rho": float(dens_lb),
        "density_lower_bound_known_prellberg_2026": float(prellberg),
        "rho_lower_bound_from_known_density": float(prellberg / 4),
        "density_needed_in_cheeger_to_match_rho": "none: 4-4sqrt(1-rho^2) < 3.50074529 unless rho > 0.99218",
        "rho_at_which_cheeger_density_bound_reaches_3.50074529":
            math.sqrt(1 - ((4 - float(prellberg)) / 4) ** 2),
        "ratio_last_four": ratios[-4:],
        "ratio_increments_last_three": [ratios[j] - ratios[j - 1] for j in range(len(ratios) - 3, len(ratios))],
        "naive_root_bound_c31^(1/31)": C[31] ** (1 / 31),
        "epg_uncertified_extrapolation_mu": 15.0,
        "amenable_value_mu": 16,
        "reading": [
            "Ratios c_n/c_{n-1} still increase (~12.1 at n=31) with slowly decreasing increments; "
            "they are consistent with mu ~ 15 (EP-G extrapolation, uncertified) and do not exclude mu = 16.",
            "The certified bound 16 theta = 13.2693 is the better of the s=0 (16x16) and s=1 (15x15) Hankel certificates "
            "from these 32 terms; no finite moment list can certify mu < 16 "
            "(thompson-f-moment-data-cannot-certify-nonamenability).",
            "Exact extension past n = 31 needs the ball of radius ~16 of F (support grows ~2.72x per step, "
            "10,133,856 at radius 15): ~1e13 group elements, beyond this machine (4 cores, 15 GB).",
            "Via Cheeger-Mohar the certified norm bound gives density >= 2.3475 only; the combinatorial "
            "density 3.50074529 is stronger, and conversely density 3.5 gives only rho > 0.8752. "
            "The two certified quantities are not comparable by these inequalities.",
        ],
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
