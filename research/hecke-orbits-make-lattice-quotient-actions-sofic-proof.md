---
rg: 2
id: hecke-orbits-make-lattice-quotient-actions-sofic-proof
kind: route
title: Benoist-Quint Corollaire 1.2(c) equidistributes distinct finite orbits, and equidistributed finite orbits give soficity
target: hecke-orbits-make-lattice-quotient-actions-sofic
requires:
  - benoist-quint-zariski-dense-invariant-measures-are-haar
  - finite-equidistributed-orbits-give-sofic-action
---

1. **Equidistribution.** Let `X_1, X_2, ...` be distinct finite `Γ`-orbits in `X = G/Λ`. `G` is connected with
   simple Lie algebra, `Λ` is a lattice, and `Γ` is a Zariski-dense subgroup, hence sub-semigroup. By
   Corollaire 1.2(c) of Benoist--Quint (`benoist-quint-zariski-dense-invariant-measures-are-haar`),
   `(1/|X_n|) Σ_(x ∈ X_n) δ_x` converges to the Haar probability measure on continuous compactly supported
   functions, which is the convergence in the statement of the criterion.
2. **Soficity.** `X` is second countable, locally compact and Hausdorff. `Γ` acts by homeomorphisms,
   preserves Haar measure, and is sofic. The `X_n` are finite `Γ`-invariant sets. So
   `finite-equidistributed-orbits-give-sofic-action` gives soficity. ∎

**Instance 1 check.** If `Γ_1 ∩ hΓ_2h^(−1)` has finite index in both, and `c ∈ Comm_G(Γ_1)`, put `g = ch`. Then
`gΓ_2g^(−1) = c(hΓ_2h^(−1))c^(−1)` is commensurable with `cΓ_1c^(−1)`, which is commensurable with `Γ_1`. So
`Γ_1 ∩ gΓ_2g^(−1)` has finite index in `Γ_1`, which is the stabilizer condition for a finite orbit of `gΓ_2`.

*Infinitely many orbits.* Write `C = Comm_G(Γ_1)` and `Δ = hΓ_2h^(−1)`. The set `P = {chΓ_2 : c ∈ C}` is
a union of finite `Γ_1`-orbits, and `c, c'` give the same point iff `c^(−1)c' ∈ Δ`. So
`|P| = [C : C ∩ Δ]`. If only finitely many orbits occurred, `P` would be finite, and `C ∩ Δ` would have
finite index in `C`. Now `Γ_1 ∩ Δ <= C ∩ Δ <= Δ`, and `Γ_1 ∩ Δ` has finite index in `Δ`, so `Γ_1 ∩ Δ` has
finite index in `C`. Then `Γ_1` has finite index in `C`, contrary to the assumption
`[C : Γ_1] = ∞`. Lattices are Zariski dense by Borel density (recalled), which covers the hypothesis on
`Γ_1`.
