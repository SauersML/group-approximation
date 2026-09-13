---
rg: 2
id: radu-nilpotent-by-arithmetic-quotients-are-sofic
kind: claim
title: The free-nilpotent-by-arithmetic quotients of Radu's BMW lattice are sofic
distinct_from:
  radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups: that proves the marked-limit reduction; this asks for the soficity of the approximating groups
  finite-rank-holonomy-extensions-of-vfree-actors-are-sofic: that proves soficity of amenable-kernel extensions of virtually free groups with a regular finite-rank realization; here the quotient is a higher-rank arithmetic lattice, not virtually free
---

**OPEN.** For every `k >= 2` the group `G_k = Γ_R/γ_k(Λ_v)` of
`radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups` is sofic. By that claim this implies
`radu-bmw-lattice-sofic` (`radu-bmw-lattice-sofic-via-nilpotent-by-arithmetic-quotients`).

## Attempts

* **General permanence.** Amenable-by-sofic permanence would give it, but it is open even for
  finite cyclic kernels (`binary-jacobson-weak-sofic-status-proof`, Section 5).
* **Residual finiteness and amenability.** Dead. `G_k` is not residually finite, and not LEF
  for large `k`. A residually amenable approximation must see `(xz)^4` in an amenable quotient.
* **The split host for `k = 2`.** `G_2 <= (C_1/B_1)(T_h × Y) ⋊ Q`. `C_1 ⋊ Q` is a direct-sum
  lamp group over the sofic `Q`-set of edges, and it is sofic by Gao–Kunnawalkam
  Elayavalli–Patchell Theorem A, as cited in `free-wreath-over-amenable-action-is-sofic`.
  The host is its quotient by the boundary submodule `B_1`, and soficity does not pass to
  quotients. Dies there.
* **Finite chain models.** Dead for exact congruence models. Let `N <= Q` be of finite index.
  In `X_N = N\(T_h × Y)`, the strips of squares between a vertical `(xz)^2`-cycle and its
  horizontal translate give `[ℓ_p] = ±[ℓ_(hp)]`, with sign `−1` exactly for the letter `c`,
  because `cδ^2c = δ^(−2)`. A horizontal cycle with an odd number of `c`'s through `p` gives
  `2[ℓ_p] = 0`. This is the homological shadow of `(xz)^4 ∈ Γ_0`. A sofic model must either
  avoid odd horizontal holonomy on most points, or break these strips at a sparse set of
  defects. The horizontal slices of congruence models are Cayley graphs of congruence quotients
  of the Zariski-dense free product `A`, which are expected to be expanders by
  super-strong approximation (not checked here). So sparse defects do not break the strips.
