---
rg: 2
id: kazhdan-nv-exceptional-set-has-a-displacement-gap
kind: claim
title: For a Kazhdan pair (Q, ε) the minimal displacement max_q ||q_*ν - ν||_1 over probability measures is 0 or at least ε², so for an infinite Kazhdan subgroup of nV it is at least ε² on the exceptional set, and its Kazhdan projection vanishes in every reduced germ algebra of an infinite minimal set
distinct_from:
  kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures: that proves invariant measures live on U_K through the potential of an invariant measure; this is a quantitative gap for all probability measures, not only invariant ones, which converts every vanishing-error transport construction and every reduced-algebra Kazhdan-projection argument into the target itself.
  kazhdan-groups-mean-free-amenable-iff-residually-finite: that pushes almost invariant means onto finite orbits for abstract Kazhdan groups; this records the measure-class version with explicit threshold ε² on a compact space and applies it to the exceptional set Z_K of nV and to germ-groupoid algebras.
  finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite: that gives a spectral gap on single orbit Schreier graphs; this gives the gap for diffuse measures and for pushforwards of windows on arbitrary invariant covers, and separates the maximal and reduced germ algebras.
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

**ESTABLISHED** by `kazhdan-nv-displacement-gap-proof` (agent-verified only, no referee
pass as of 2026-09-17).

## Statement

Let `K` be a countable group with Kazhdan pair `(Q, ε)` acting on a compact metrizable
`Z`, and `D_Q(ν) = max_{q∈Q} ||q_*ν - ν||_1` on `Prob(Z)`.

1. **Zero-one law.** `min_{Prob(Z)} D_Q` exists and is `0` if `Z` carries a `K`-invariant
   probability measure, and `>= ε²` otherwise.
2. **Windows project.** If a standard Borel `K`-space `Y` with invariant σ-finite `λ` maps
   equivariantly to `Z` and has `W` with `0 < λ(W) < ∞`, `λ(qWΔW) < ε²λ(W)` for `q ∈ Q`,
   then `Z` carries an invariant probability measure.
3. **nV.** For an infinite Kazhdan `K <= nV`, `Z_K ≠ ∅` and `D_Q(ν) >= ε²` for every
   `ν ∈ Prob(Z_K)`. The target
   `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures` is equivalent to
   the existence, on each minimal set, of one `ν` with `D_Q(ν) < ε²`.
4. **Kazhdan projection.** For Kazhdan `K <= nV` and closed invariant `Z`, the image of
   `p_K` in the reduced germ algebra `C*_r(G_K|Z)` is nonzero iff `Z ∩ U_K ≠ ∅`, and in
   the maximal germ algebra iff `Z` carries an invariant probability measure. On an
   infinite minimal `Z` the reduced image is `0`, so the target on `Z` is nonvanishing
   inside the kernel of `C*(G_K|Z) -> C*_r(G_K|Z)`.

## Class killed

Vanishing-error measure transport (brick transport with shrinking bad sets, Følner windows
on skew products or orbit covers) and Kazhdan-projection transplants certified by reduced
norms (regular or quasi-regular representations, ghost projections, coarse estimates,
reduced K-theory, conditional expectation onto `C(Z)`) are each equivalent to the target
or see `0`. Invariant where they die: `m_Q(Z_K) >= ε²` in a counterexample, and the kernel
of the max-to-reduced quotient. A proof has to produce displacement below `ε²` in one step
through an exact nV mechanism. Details: artifact Sections A, B.
