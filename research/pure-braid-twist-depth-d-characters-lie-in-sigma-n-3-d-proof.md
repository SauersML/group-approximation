---
rg: 2
id: pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d-proof
kind: route
title: "Downward induction over zero multicurves, running Meier–Meinert–VanWyk on the links of the curve complex"
target: pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d
requires: []
artifacts:
  - research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md
---

Complete proof in the artifact, Section 4. It uses Lemmas 1 to 5 of Section 2 and
the tools (T1), (T2) of Section 1, the same as the proof of
`pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3`.

- Lemma 5: the link of a multicurve with `s` curves is the join of the curve
  complexes of the `s + 1` complementary pieces (spheres with `k_P` marked
  points, `sum k_P = n + 1 + 2s`), hence `(n - 4 - s)`-connected by Harer and
  Milnor's join formula.
- Lemma 6: if `d <= n - 3`, then every simplex stabilizer contains a twist with a
  nonzero value. Extend the simplex to a pants decomposition with `n - 2 > d`
  curves; some curve has nonzero type.
- Lemma 7: let `l = n - 3 - d`. For a zero multicurve `sigma` with `s` curves
  (`s <= d`), `[chi|Stab(sigma)]` is in `Sigma^l`. Induct downward on `s` with
  (T1) for `Stab(sigma)` on `L(sigma)`. It is `(l-1)`-connected because
  `s <= d`. A cell `rho` either adds a curve of nonzero type (then (T2) applies)
  or gives a larger zero multicurve (induction, level `l >= l - dim rho`).
- Theorem: (T1) for `P_n` on `C` at level `l`. Vertex and cell stabilizers are
  handled as in Lemma 7.
- One-block exactness: generic weights on `A` vanish on `B` iff
  `|B ∩ A| <= 1` or `B ⊇ A`. A chain through one point of `A` gives `d >= n - |A|`.
  The tree count `sum (children - 1) = n - 1`, applied with the smallest node
  containing `A` (at least `|A|` children), gives `d <= n - |A|`.
- Non-sharpness examples: Aomoto cohomology computed in
  `experiments/pure-braid-bnsr-complements-are-real-res-2026-09-16/`
  (`H^1 = 0` on `c_12 = c_34 = 0` in `P_5`; exact over `Q` since the dimension
  vanishes mod `p`), plus the product-projection claim for two triples.
