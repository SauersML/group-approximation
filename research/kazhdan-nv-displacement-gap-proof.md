---
rg: 2
id: kazhdan-nv-displacement-gap-proof
kind: route
title: Half-densities of a measure with small displacement are almost invariant in the Koopman representation of its quasi-invariant saturation, and the Kazhdan projection of a regular germ representation sees only germ-finite points
target: kazhdan-nv-exceptional-set-has-a-displacement-gap
requires:
  - kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

Complete proofs: artifact Sections A and B. Imports: defining form of (T) with a Kazhdan
pair; Kazhdan groups are finitely generated and finite-index subgroups are Kazhdan; the
Kazhdan projection in `C*_max(K)` maps to the projection onto invariant vectors in every
unitary representation. The only graph prerequisite is Corollary 4 of the criterion
(`Z_K` nonempty with no invariant probability measure for infinite Kazhdan `K`).

1. **Zero-one law.** For `ν` with `D_Q(ν) < ε²`, saturate to `ν̄ = Σ c_g g_*ν`. In the
   Koopman representation on `L²(ν̄)`, `ξ = (dν/dν̄)^{1/2}` satisfies
   `||π(q)ξ - ξ||² <= ||q_*ν - ν||_1 < ε²` by `(√a - √b)² <= |a - b|`. (T) gives
   `η ≠ 0` invariant, and `|η|²ν̄` is invariant. `D_Q` is weak-* lsc (Riesz duality), so
   the minimum is attained.
2. **Windows.** `p_*(λ|_W)/λ(W)` has displacement `<= λ(qWΔW)/λ(W)`.
3. **nV.** Apply 1 to `Z_K`; finitely supported measures on infinite orbits have
   displacement `>= ε²` because an invariant measure on a countable set has a finite orbit.
4. **Kazhdan projection.** In a regular germ representation `ρ_x` the image of `p_K` is
   the projection onto `K`-invariant vectors of a permutation representation on germs, so
   it is nonzero iff some point has finitely many germs, iff it lies in `U_K` (finite
   generation of the trivial-germ subgroup). The Koopman pair of an invariant measure is
   a germ representation with invariant vector `1`; conversely an invariant vector gives
   an invariant state on `C(Z)`.
