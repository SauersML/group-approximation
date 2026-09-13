---
rg: 2
id: hopf-doubling-tower-has-no-m2-but-divides-unit-tracially
kind: claim
title: The Hopf doubling tower contains no copy of M_2, yet divides its unit tracially over every closed set of extreme traces
distinct_from:
  stw27-coordinate-euler-slack-obstructs-compact-dividers: that uses coordinate Euler mass to exclude compact dividers in Villadsen limits; this exhibits a tower where the obstruction excludes every nonzero M_2 but the unit is still tracially divisible over every closed face, so compact invariants do not reach face bundles.
  r-fibre-w-star-bundles-divide-the-unit-uniformly: that asks whether every hyperfinite W*-bundle divides its unit; this is one model where the answer is yes although no finite stage has a nonzero square subbundle.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Let `X_1 = S²` and `q_1 = L`, the Hopf line bundle. Put `X_{n+1} = X_n × X_n`,
`q_{n+1} = π_1*q_n ⊕ π_2*q_n` and `φ_n(a) = π_1*a ⊕ π_2*a`. Let
`A = lim q_n(C(X_n) ⊗ K)q_n`, so that `q_n ≅ ⊕_{c ≤ 2^{n−1}} L_c` over `(S²)^{2^{n−1}}`.
1. No building block, and not `A` itself, has nonzero orthogonal Murray–von Neumann
   equivalent projections. So there is no nonzero `*`-homomorphism `M_2 → A`.
2. For every nonempty closed `K ⊆ ∂_e T(A)` and every `N`, the unit of `A` is tracially
   `N`-divisible relative to `K`. The W*-bundle over `K` is trivial.

**Meaning.** Villadsen-type unit rigidity is a norm and compact phenomenon, like
DHTW's missing `Z_{3,4}` or coordinate Euler slack. It does not produce a
projection-starved W*-bundle. A witness for
`nontrivial-w-star-bundle-with-r-fibres-exists` through a divisibility gap must defeat
central halving relative to the face, not merely compact dividers.

**Model test.** Part 1 is the degenerate end of the coordinate Euler criterion:
Euler mass fraction `1`, forcing the divider rank to `0`. Part 2 is the real object
satisfying the hypothesis of `central-halving-trivializes-every-closed-bauer-face-bundle`.
