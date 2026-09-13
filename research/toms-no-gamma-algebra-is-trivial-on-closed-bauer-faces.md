---
rg: 2
id: toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces
kind: claim
title: Toms's no-Gamma algebra has central halving, so its W*-bundle over every closed set of extreme traces is trivial
distinct_from:
  toms-ah-counterexample-to-uniform-gamma: that is the existence of a simple AH algebra without uniform Gamma; this shows that the failure is invisible over every closed set of extreme traces, so the algebra answers no Bauer question through its faces.
  toms-doubling-ah-trace-simplex-is-poulsen: that shows the whole trace simplex is not Bauer; this shows that restricting to any closed Bauer face does not rescue a witness either.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Let `B` be Toms's simple, separable, unital, nuclear AH algebra without uniform
property Γ (arXiv:2606.12188v2, Theorem 5), or his non-simple Thom–Porteous tower
(Section 4).
1. `B` has central halving: norm-central projections `p_j` with
   `sup_{τ∈T(B)} |τ(p_j) − 1/2| → 0`.
2. For every nonempty closed `K ⊆ ∂_e T(B)`, the W*-bundle `M_K` over `K` is trivial,
   and the unit of `B` is tracially `N`-divisible relative to `K` for every `N`.
3. So `B` separates central halving from uniform property Γ. The two agree on Bauer
   simplices (CETW Proposition 3.1), and here the gap is carried entirely by limit
   traces that do not lie in any closed set of extreme traces.

**Effect on Question 3.14.** Toms's certificate is a pair of equal-trace projections
that are not equivalent in the completion. It never restricts to a closed face. So
`B`, its non-simple tower, and every other block-balanced tower give no witness for
`nontrivial-w-star-bundle-with-r-fibres-exists` through any face.

**A concrete infinite-dimensional face.** In the non-simple tower, the diagonal branch
traces with free labels `z_{i+1} = (z_i, z_i, ℓ_i)` form a closed set of extreme traces
homeomorphic to `Gr(d,2d) × Π_i CP^{j_i}`. That set contains a Hilbert cube. The
R-fibre bundle over it is still trivial.
