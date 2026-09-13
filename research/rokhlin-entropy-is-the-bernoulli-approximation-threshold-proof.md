---
rg: 2
id: rokhlin-entropy-is-the-bernoulli-approximation-threshold-proof
kind: route
title: Models from Corollary 6.1 give the approximation, upper semicontinuity gives the bound, and bases above the supremum give AINV iff INF
target: rokhlin-entropy-is-the-bernoulli-approximation-threshold
requires:
  - seward-approximate-bernoulli-models-and-semicontinuity
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - bernoulli-entropy-counterexample-constraints
---

"Item A.n" refers to `seward-approximate-bernoulli-models-and-semicontinuity`.
"Theorem 1.10" and "Theorem 1.1" refer to the imports in the second and third
prerequisites.

**Topology.** `E_G(L^G)` has the subspace topology of the compact metrizable space of
Borel probability measures on `L^G`. So closures are sequential closures.

**Item 1.** Let `U` be an open neighbourhood of `λ^G` in `E_G(L^G)`. Item A.1 gives a
`G`-equivariant isomorphism `φ: (X, μ) → (L^G, ν)` with `ν ∈ U`. The measure
`ν = φ_* μ` is ergodic and invariant, and `G ↷ (L^G, ν)` is isomorphic to `X`. So
`ν ∈ M_L(X) ∩ U`.

**Item 2.** Take `ν_n ∈ M_L(X)` with `ν_n → λ^G`. Rokhlin entropy is an isomorphism
invariant, so `h^Rok_G(L^G, ν_n) = h^Rok_G(X)` for every `n`. The Bernoulli measure
`λ^G` is ergodic, so it lies in `E_G(L^G)`, and item A.2 gives

    h^Rok_G(L^G, λ^G) ≥ limsup_n h^Rok_G(L^G, ν_n) = h^Rok_G(X).

Theorem 1.10 gives `h^Rok_G(L^G, λ^G) = min(H(λ), s)`.

**Item 3.** Probability vectors on finite sets realize every value in `[0, ∞)` as
Shannon entropy.
- If `h^Rok_G(X) < ∞`, item 1 shows that every `t > h^Rok_G(X)` is the entropy of an
  approximated `λ`. So the infimum is at most `h^Rok_G(X)`.
- By item 2, every approximated `λ` has `H(λ) ≥ h^Rok_G(X)`. So the infimum is at
  least `h^Rok_G(X)`.
- If `h^Rok_G(X) = ∞`, item 2 shows that no `λ` is approximated, and the infimum over
  the empty set is `∞`.

**Corollary.** A Bernoulli shift `K^G` with `H(κ) > 0` is free and ergodic, and
Theorem 1.10 gives `h^Rok_G(K^G) = min(H(κ), s)`. The two bullets are items 1 and 2
with `X = K^G`.

**AINV(G) ⟹ INF(G).** Suppose `s < ∞`. Choose finite bases with
`s < H(λ) < H(κ)`. Then `min(H(κ), s) = s < H(λ)`, so the first bullet puts `λ^G` in
the closure of `M_L(K^G)`, and AINV(G) fails.

**INF(G) ⟹ AINV(G).** Suppose `s = ∞` and `H(λ) < H(κ)`. If `λ^G` were in the
closure of `M_L(K^G)`, the second bullet would give `H(κ) = min(H(κ), ∞) ≤ H(λ)`.

**AINV(G) ⟹ INV(G).** Suppose INV(G) fails, so `L^G ≅ K^G` for standard bases with
`H(λ) < H(κ)`. By part (b) of `bernoulli-entropy-counterexample-constraints`,
`0 < H(λ) < ∞`. First reduce to finite bases.
- If `H(κ) = ∞`, let `M` be a finite base with `H(M) = 1`. Then
  `(L × M)^G = L^G × M^G ≅ K^G × M^G = (K × M)^G`. The base `K × M` has infinite
  entropy, so Theorem 1.1 gives `(K × M)^G ≅ K^G ≅ L^G`. So `L^G` is isomorphic to a
  Bernoulli shift of finite base entropy `H(λ) + 1`.
- So assume `H(κ) < ∞`. Choose finite bases `λ'`, `κ'` with `H(λ') = H(λ)` and
  `H(κ') = H(κ)`. By Theorem 1.1, `L'^G ≅ L^G ≅ K^G ≅ K'^G`.

An isomorphism `ψ: K'^G → (L'^G, λ'^G)` shows `λ'^G ∈ M_(L')(K'^G)`, which lies in
its closure, with `H(λ') < H(κ')`. So AINV(G) fails.
