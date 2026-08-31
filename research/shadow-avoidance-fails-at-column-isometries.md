---
rg: 2
id: shadow-avoidance-fails-at-column-isometries
kind: claim
title: Column isometries defeat dimension-free shadow avoidance
invalidates: [dimension-free-shadow-avoidance-in-hyperfinite-factor]
distinct_from:
  dimension-free-shadow-avoidance-in-hyperfinite-factor: that asserted a dimension-free threshold; this is its refutation by an explicit one-element family whose 2-norm vanishes while every commutant projection is fully shadowed.
  x2-local-afd-holds-at-rate-controlled-packets: that positive cell survives — its rate hypothesis delta below eps d^{-5/2} excludes this family, whose 2-norm is d^{-1/2}; together they pin the critical rate exponent into [1/2, 5/2].
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

For every `d`, write `R = M_d ⊗ R'` and pick trace-zero unitaries
`u_1,…,u_d ∈ R'`.  The column contraction

```text
z = Σ_k e_{k1} ⊗ u_k/√d
```

satisfies `‖z‖ = 1`, `E_{M_d}(z) = 0`, `‖z‖₂ = d^{-1/2} → 0`, and
`z*z = e₁₁ ⊗ 1`.  Since `e₁₁⊗1` commutes with `1⊗s'`,

```text
‖z(1⊗s')‖² = ‖(1⊗s')(e₁₁⊗1)(1⊗s')‖ = ‖e₁₁ ⊗ s'‖ = 1
```

for EVERY nonzero projection `s' ∈ R'`.  So no function `δ₀(ε, j)`
independent of `d` can exist: already at `j = 1`, for any `ε < 1` and
any `δ₀`, take `d > δ₀^{-2}`.
`dimension-free-shadow-avoidance-in-hyperfinite-factor` is refuted, and
the route `x2-via-dimension-free-shadow-avoidance` is dead.

What survives, exactly:

* The rate-controlled cell is untouched — this family sits at 2-norm
  `d^{-1/2}`, far above its `ε·d^{-5/2}` threshold.  The critical
  exponent for commutant shadow avoidance is now pinned between `1/2`
  (this refutation) and `5/2` (the spectral-cut proof).
* The refutation makes the "maximal entanglement" failure mode
  concrete: the bad subspace `e₁₁⊗1` has trace `1/d` in `R` but its
  `R'`-shadow is literally all of `R'` — a single matrix unit spread
  over the commutant by unitaries.  Any viable positive route through
  local AFD must therefore CHOOSE the finite-dimensional subfactor
  jointly with the packet so that residues never contain such
  column-isometry mass — and choosing `M` adapted to the packet is a
  reformulation of local AFD itself, so the commutant reduction buys
  no quantifier progress beyond the rate-controlled cell.  X(2) is
  unaffected in both directions: this kills a sufficient condition,
  not the problem.
