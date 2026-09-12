---
rg: 2
id: toms-doubling-ah-trace-simplex-is-poulsen
kind: claim
title: Toms's doubling AH algebras without uniform property Gamma have the Poulsen simplex as trace space
distinct_from:
  toms-ah-counterexample-to-uniform-gamma: that imports the existence of Toms's simple AH algebra without uniform Gamma; this computes the trace simplex of that algebra and of the non-simple limit, and finds the Poulsen simplex, not a Bauer simplex.
  toms-gamma-counterexample-fails-strict-comparison: that shows every AH algebra without uniform Gamma fails strict comparison; this is about the shape of the trace simplex of Toms's algebras and says nothing about comparison.
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks for a nontrivial R-fibre W*-bundle over a compact base; this shows the extreme boundary of Toms's algebras is dense and not closed, so as they stand they give no such bundle.
artifacts:
  - research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md
---

Let `A = lim (A_i, φ_i)` with `A_i = s_i (C(X_i) ⊗ K) s_i`, where `X_i` is compact
metrizable and `s_i` has constant rank. Suppose the point trace at `y ∈ X_{i+1}`
restricts to `A_i` as the measure

```text
α_i |W_i|^{-1} Σ_{w ∈ W_i} δ_{λ_{i,w}(y)} + (1 − α_i) ν_i(y),     Σ_i (1 − α_i) < ∞,
```

with `|W_i| ≥ 2`, continuous `λ_{i,w} : X_{i+1} → X_i`, and probability measures
`ν_i(y)`. Suppose also:
- **(D)** there are maps `d_i` with `λ_{i,w} ∘ d_i = id` for every `w`;
- **(F)** the joint map `(λ_{i,w})_w : X_{i+1} → X_i^{W_i}` is surjective.

Then `∂_e T(A)` is dense in `T(A)`. If some `X_i` has two points, `T(A)` is the
Poulsen simplex, so `∂_e T(A)` is not closed and `T(A)` is not Bauer.

Both of Toms's algebras (arXiv:2606.12188v2) satisfy these hypotheses:
- the non-simple limit of Section 4, with `α_i = 1`, `λ = π_1, π_2` on
  `X_i × X_i × CP^{j_i}`, and the diagonal as `d_i`;
- the simple algebra `B` of Proposition 4. Its telescoped top maps average over
  `2^{k_i}` leaves, and its point-evaluation part has summable normalized rank.

So neither trace simplex is Bauer. The algebra of
`toms-ah-counterexample-to-uniform-gamma` does not by itself answer BBSTWW
Question 3.14 (`nontrivial-w-star-bundle-with-r-fibres-exists`).

Toms evaluates his Thom–Porteous obstruction with diagonal branch traces (his
Lemma 2 and Proposition 4(3)). These are exactly the extreme traces shown here to
be dense.
