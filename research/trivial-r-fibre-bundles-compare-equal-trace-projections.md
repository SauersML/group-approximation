---
rg: 2
id: trivial-r-fibre-bundles-compare-equal-trace-projections
kind: claim
title: In the trivial hyperfinite W*-bundle over any compact base, equal-trace projections are approximately equivalent
distinct_from:
  r-fibre-w-star-bundle-finite-dim-base-is-trivial: that is Ozawa's triviality theorem for finite-dimensional bases; this is a property of the trivial bundle over every compact base, used as an invariant that certifies nontriviality with no dimension hypothesis.
  strict-comparison-compares-ultrapower-projections: that compares projections in the tracial ultrapower of a C*-algebra with strict comparison; this compares projections of equal trace function in the abstract trivial bundle C_σ(K,R), with no C*-algebra and no comparison hypothesis.
  toms-ah-counterexample-to-uniform-gamma: that is an algebra whose uniform tracial completion has equal-trace non-equivalent projections; this is the bundle-level statement that such projections can never occur in a trivial bundle.
artifacts:
  - research/artifacts/tw-hilbert-cube-projection-invariant-2026-09-12.md
---

Let `K` be a compact Hausdorff space, and let `P, Q ∈ C_σ(K,R)` be projections
with `τ(P(λ)) = τ(Q(λ))` for every `λ ∈ K`. For every `ε > 0` there is
`W ∈ C_σ(K,R)` with `‖W‖ ≤ 1`, `W = QWP`, `‖W*W − P‖_{2,u} ≤ ε` and
`‖WW* − Q‖_{2,u} ≤ ε`.

**Nontriviality criterion.** Let `M` be a W*-bundle over `K` with every fibre
`R`. Suppose it contains projections `P, Q` with `E(P) = E(Q)`, such that the
infimum of `max(‖W*W − P‖_{2,u}, ‖WW* − Q‖_{2,u})` over contractions
`W = QWP` in `M` is positive. Then `M` is not isomorphic to `C_σ(K,R)`.
Isomorphisms of W*-bundles preserve `E` and `‖·‖_{2,u}`.

**Proof idea.**
- Cover `K` by finitely many open sets on which a constant partial isometry is a
  good approximate equivalence.
- Realize a continuous partition of unity by orthogonal projections
  `χ_{[s_{i−1}(λ), s_i(λ))}(h)`, where `h` is a Lebesgue-distributed self-adjoint
  in the relative commutant of a finite-dimensional subalgebra carrying all the
  data. These projections are exactly central for that data and continuous in `λ`.
- Glue, and compress into the corner.

No covering-dimension hypothesis is used. The full proof is in the artifact.

**For BBSTWW Question 3.14** (`nontrivial-w-star-bundle-with-r-fibres-exists`),
a witness bundle over a Hilbert cube can be certified by exhibiting equal-trace
projections that are not approximately equivalent. This is the bundle form of
Toms's Thom–Porteous obstruction to uniform property Gamma.
