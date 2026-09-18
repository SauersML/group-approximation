---
rg: 2
id: spatial-two-graph-realizations-in-g2n-leave-the-degree-plane
kind: claim
title: A spatial realization of a finite 2-graph groupoid with rho(M_1) > 1 inside the Cuntz product groupoid G_2^n has a letter-count class outside the degree plane
artifacts:
  - research/artifacts/nv-bernoulli-conformal-class-kill-2026-09-17.md
distinct_from:
  two-graph-brick-codings-are-rigid-under-rank-two-h1: that uses one measure (Lebesgue) and the Kraft equality on edge-wise brick codings, and needs row sums that are not powers of 2 or a SAT step; this uses the whole Bernoulli family on arbitrary spatial groupoid realizations and needs no hypothesis on row sums.
  brick-coded-two-graph-full-groups-embed-in-brin-thompson: that builds embeddings from brick codings; this is an obstruction to every spatial realization, brick-coded or not.
  finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite: that characterizes finite subgroups of nV by bounded offset transfer; this proves a groupoid-level obstruction that combines bounded transfer with Perron pinning of Bernoulli Radon-Nikodym classes.
---

**Setting.**
- `G_2^n` is the Cuntz product groupoid of triples `(x, k, y)` with `x, y ∈ ({0,1}^N)^n`,
  given by coordinatewise prefix replacement.
- `N^ε_i(uw, k, vw) = #_ε(u_i) - #_ε(v_i)` are its letter-count cocycles, for `ε ∈ {0,1}`
  and `1 ≤ i ≤ n`.
- `Λ` is a finite 2-graph without sources. `G_Λ` is its path groupoid, with degree cocycles
  `d_1` and `d_2`. `M_1` and `M_2` are its colour matrices.
- A **spatial realization** is a continuous groupoid homomorphism `ι : G_Λ -> G_2^n` whose
  restriction to the unit space is a homeomorphism onto a compact open subset of
  `({0,1}^N)^n`. Neither injectivity nor openness of `ι` off the units is assumed.

**Claim.**
- **(i) Theorem.** If `ρ(M_1) > 1`, then for every spatial realization `ι` the classes
  `[N^ε_i ∘ ι] ∈ H^1(G_Λ; R)` are not all in `R[d_1] + R[d_2]`. Here `H^1` means continuous
  cocycles modulo coboundaries of continuous functions.
- **(ii) Rigidity corollary.** Suppose, in addition, that every locally constant real
  cocycle on `G_Λ` is cohomologous to some `a d_1 + b d_2`. Then `G_Λ` has no spatial
  realization in any `G_2^n`.

Mechanism, called the Bernoulli conformal class:
- Each Bernoulli measure `μ_p` pulls back to a quasi-invariant measure with Radon–Nikodym
  cocycle `D_p∘ι = Σ_i N^1_i∘ι log p_i + N^0_i∘ι log(1-p_i)`.
- Perron–Frobenius pins the degree-plane part of that class at `-log ρ(M_j)`, for every `p`.
- So all letter classes vanish, the offset cocycles have bounded transfer, and the source
  fibres of `ι(G_Λ)` are bounded, while column sums of `M_1^j` are unbounded.

Route: `spatial-two-graph-realization-bernoulli-pinning-proof`.
