---
rg: 2
id: fpbs-mal-graphing-b-length-weighted-floor
kind: claim
title: Every graphing that generates F(a,b) over K = <a, bab^-2> on a free action weakly contained in Bernoulli has double-coset b-length weighted mass at least 1/80
distinct_from:
  fpbs-weakly-bernoulli-fold-seeds-have-density-floor: that bounds seed sets for the single label b, i.e. graphings inside K b K; this covers graphings with arbitrary labels, weighted by their double-coset b-length, and reduces to that claim.
  fpbs-mal-bernoulli-single-stage-floor: that asks for an unweighted positive floor over all graphings; this gives the length-weighted floor, which is unweighted only for bounded b-length.
  fpbs-relative-fixed-price-free-pairs: that predicts relative cost 0 at this pair; this shows any witness needs average double-coset b-length at least 1/(80 epsilon) at mass epsilon.
  fpbs-malnormal-coset-cycles-linear-perimeter: that is a floor for packing certificates with bounded detours; this is a floor for all generating graphings, with the weight counting b-letters modulo K on both sides.
artifacts:
  - research/artifacts/fpbs-chord-unfolding-length-floor-2026-09-18.md
  - experiments/fpbs-chord-unfolding-2026-09-17/coset_b_length.py
  - experiments/fpbs-chord-unfolding-2026-09-17/coset_b_length_out.txt
  - experiments/fpbs-chord-unfolding-2026-09-17/stallings_membership.py
  - experiments/fpbs-chord-unfolding-2026-09-17/stallings_membership_out.txt
  - experiments/fpbs-chord-unfolding-2026-09-17/chord_threshold.py
  - experiments/fpbs-chord-unfolding-2026-09-17/chord_threshold_N12_M4_out.txt
---

**ESTABLISHED** through `fpbs-mal-graphing-b-length-weighted-floor-proof`.

Let `L = F(a, b)` and `K = <a, b a b^{-2}>`. For `h ∈ L`, let `|h|_{K,b}` be
the least `r` with `h ∈ K b^{±1} K b^{±1} ⋯ b^{±1} K` (`r` letters
`b^{±1}`).

**Claim.** Let `L` act freely and p.m.p. on `(X, μ)`, weakly contained in a
Bernoulli shift of `L`. Let `Φ = ⊔_j h_j|_{D_j}` be a graphing with
`R_K ∨ Φ = R_L`, with one label per piece. Then

```text
Σ_j |h_j|_{K,b} μ(D_j)  ≥  σ_b(X)  ≥  1/80 .
```

**Consequences** (artifact §3).
- Graphings with all labels of `b`-length `≤ r` have mass `≥ 1/(80 r)`.
  This is uniform in the number of labels, in the `K`-letters, and in word
  length. At `r = 1`, `relC_{≤1} = σ_b` exactly.
- A generating graphing of mass `ε` puts weighted mass `≥ 1/160` on labels of
  `b`-length `> 1/(160 ε)`.
- `Gamma_mal`, with the Bernoulli shift `β` or any free action weakly
  contained in it: a witness of `relC(E_{H_2}; E_{H_1}) = 0` needs average
  `b_2`-length tending to infinity. A stagewise scheme with
  `b_{n+1}`-lengths `≤ r_n` has mass `≥ Σ 1/(80 r_n)`, so it needs
  `Σ 1/r_n < ∞`.

**Not covered.**
- Unweighted floors: sharing of unfolded seeds between long chords (artifact
  §5, P1 and P2).
- Non-stagewise graphings of `E_β` with deep labels (P3).
