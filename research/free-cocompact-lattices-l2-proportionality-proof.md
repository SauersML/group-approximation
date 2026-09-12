---
rg: 2
id: free-cocompact-lattices-l2-proportionality-proof
kind: route
title: Harmonic diagonals are automorphism-invariant and Haar unfolding counts orbits
target: free-cocompact-lattices-proportional-l2-betti
requires: []
artifacts:
  - research/artifacts/atiyah-lattice-transfer-2026-09-12.md
---

Derivation. The full text, with the setup and orientation conventions, is in the artifact.

Let `H = Aut(X)` with the permutation topology on vertices. It is totally disconnected
and locally compact with compact open simplex stabilizers `H_σ`. It acts unitarily on
`C^k = ℓ²(X_k)` by signed permutations, commuting with the coboundaries, hence with
`Δ_k` and with the projection `P_k` onto `ker Δ_k`.

1. **Trace formula.** For `D ≤ H` discrete, free on simplices and cocompact,
   `C^k ≅ ℓ²(D)^(n_k)` equivariantly, and for a closed `D`-invariant subspace `V`,
   `dim_(N(D)) V = Σ_(σ in D\X_k) <P_V δ_σ, δ_σ>`. The sum is independent of
   representatives, since signs cancel on the diagonal.
2. **Local invariance.** `p(σ) = <P_k δ_σ, δ_σ>` is constant on `H`-orbits, because
   `h` commutes with `P_k` and `ε(h,σ)² = 1`.
3. **Unfolding.** `H` contains a lattice, so it is unimodular; fix Haar `μ`. For an
   `H`-orbit `O` and `σ in O`, the double cosets `D\H/H_σ` correspond to `D\O`. Each
   piece `D\DxH_σ` is the injective image of `xH_σ`, because
   `D ∩ xH_σx^-1 = Stab_D(xσ) = 1`. Hence `|D\O| μ(H_σ) = μ(D\H)`.
4. **Conclusion.** `b_k^(2)(X;D) = Σ_(O in H\X_k) |D\O| p_O
   = μ(D\H) Σ_O p_O / μ(H_(σ_O))`. The sum over `O` does not depend on `D`, so the
   ratio of the values for `Γ` and `G` is `μ(Γ\H)/μ(G\H)`. By step 3 at vertex
   orbits, this equals `|Γ\X_0|/|G\X_0|`. ∎
