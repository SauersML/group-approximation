---
rg: 2
id: torsion-free-matrix-trace-defect-exists
kind: claim
title: Some torsion-free group has a projection over its reduced C*-algebra whose trace is not an integer
distinct_from:
  kadison-kaplansky-counterexample-exists: that asks for a 1x1 projection of C*_r(G) other than 0 and 1; this asks for a matrix projection of non-integer trace. The two are equivalent once the group may change, by the routes between them.
  algebraic-strong-atiyah-counterexample-exists: that asks for an algebraic matrix with non-integer von Neumann kernel dimension; this asks for any projection over C*_r with non-integer trace. A spectrally isolated Atiyah failure gives one.
---

**OPEN.** There is a countable torsion-free group `Γ` and a projection `p ∈ M_n(C*_r Γ)` with
`τ_*(p) = sum_i τ(p_ii) ∉ Z`. This is the negation of the torsion-free trace conjecture
`τ_*(K_0(C*_r Γ)) ⊆ Z`.

**Equivalent to `kadison-kaplansky-counterexample-exists`.**
- Route `kk-counterexample-via-g-star-z-scalarization`: a witness `p` over `Γ` gives a
  nontrivial projection over `Γ * Z`, by `fractional-matrix-trace-gives-projection-in-g-star-z`.
- Route `matrix-trace-defect-from-kk-counterexample`: a nontrivial projection is a `1x1` witness.

**Finite witness form.** By continuous functional calculus, `p` may be taken to be
`χ_(-∞,c)(a)` for a self-adjoint `a ∈ M_n(Z[i][Γ])` whose reduced spectrum misses `c`. The
support of `a` generates a finitely generated subgroup carrying the same witness.

## Attempts

- **Where a witness must live.** Reduced assembly must fail to be surjective for `Γ`, since its
  image has integer traces (`assembly-image-traces-are-integral-for-torsion-free-groups`). So
  `Γ` is not a-T-menable, not hyperbolic and not a real-rank-one lattice.
- **Spectral arithmetic: no force.** The fence
  `kk-half-mass-measures-pass-arithmetic-at-every-capacity` is stated for `1x1` measures, and
  its family is already `1x1`. So moments, zeta integrality and capacity bounds cannot certify
  integer traces at any matrix size either.
- **Unconditional completions on torsion-free Lie subgroups.** By
  `unconditional-spectra-of-kk-witnesses-cross-the-gap`, item 4, a witness `a ∈ M_n(Z[i][Γ])` on
  a torsion-free discrete subgroup of a reductive Lie group has spectrum in every unconditional
  completion crossing the reduced gap.
- **Small capacity is algebraic, for matrices too.** `integral-spectra-of-small-capacity-are-finite`
  is stated for `T ∈ M_n(Z[i][Γ])`. A witness `a` whose spectrum has capacity below `1` has finite
  spectrum, so `p` is an idempotent of `M_n(Qbar[Γ])` with non-integer trace. On torsion-free
  discrete subgroups of reductive Lie groups this is excluded by
  `unconditional-spectra-of-kk-witnesses-cross-the-gap`, item 1. A witness that is not already
  algebraic needs capacity at least `1`.
- **Selfless hosts need no free product.** On torsion-free groups with selfless reduced algebra
  (free products, acylindrically hyperbolic, Zariski-dense in `PSL(d,R)`, linear with trivial
  amenable radical), a witness over `Γ` already gives a nontrivial projection of `C*_r(Γ)`, by
  `selfless-projection-traces-equal-k0-trace-image`. The Fournier--Facio group is in none of these
  classes as far as main records. It is minimally almost periodic and finitely generated, hence not
  linear, and whether it is acylindrically hyperbolic is not recorded.
- **Gapped Atiyah failures and lattice transfer.** Corollary C of
  `fractional-matrix-trace-gives-projection-in-g-star-z` supplies two shapes: an algebraic
  matrix with non-integer kernel dimension and spectrally isolated kernel, or a complex as in
  `complex-with-irrational-and-torsion-free-lattices` with a Laplacian gap at `0`. Neither is
  known to exist; the published irrational L²-Betti examples are lamplighters with torsion.
