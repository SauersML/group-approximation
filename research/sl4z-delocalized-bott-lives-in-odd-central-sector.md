---
rg: 2
id: sl4z-delocalized-bott-lives-in-odd-central-sector
kind: claim
title: For the block-swap involution torus of SL_4(Z), the joint sector Bott indices vanish where -I acts by +1 and are antisymmetric in the eigenvalue of g where -I acts by -1
distinct_from:
  weak-matricial-stability-kills-centralizer-even-cohomology: that is the open general realization statement for torsion centralizers of linear groups; this is an established constraint on where, inside SL_4(Z), any realization of the block-swap centralizer class must live, and it holds for every asymptotic homomorphism.
  laurent-sl4-not-matricially-stable-for-q-at-least-4: that uses the Weyl antisymmetry beta_omega = -beta_omega-bar of a diagonal torsion element to push the Laurent class to nonreal eigenvalues; here the torsion is an involution, both eigenvalues are real, and the class is pushed instead to the -1 eigenspace of the center.
  sl4z-involution-centralizers-have-rational-h2: that computes the centralizer cohomology; this constrains asymptotic homomorphisms that could detect it.
artifacts:
  - research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md
---

**ESTABLISHED** by `sl4z-odd-central-sector-bott-proof` (lane proof, elementary, not
reviewed; no priority claimed).

## Setting

- `G = SL_4(Z)`. `g = [[0, I], [I, 0]]`, `c = −I_4`, `h = diag(1, 1, −1, −1)`.
- `M_1`, `M_2` are the commuting elements of `Z_G(g)` from
  `sl4z-involution-centralizers-have-rational-h2`. They detect `H^2(Z_G(g); Q) = Q`.
- `F = {1, g, c, cg} ≅ (Z/2)^2`. Its characters are `χ_{ε,δ}`, with `χ(g) = ε` and
  `χ(c) = δ`, for `ε, δ ∈ {±1}`.
- For an asymptotic homomorphism `φ_n : G → U(k_n)`, put
  `a_{ε,δ} = ¼ Σ_{f ∈ F} χ_{ε,δ}(f) φ_n(f)`. Let `Q_{ε,δ}` be the spectral projection of
  `(a + a^*)/2` on `[½, ∞)`. Define
  `β_{ε,δ}(φ_n) = Bott(pol(Q φ_n(M_1) Q), pol(Q φ_n(M_2) Q))` on `Q C^{k_n}`, with `Q = Q_{ε,δ}`.

## Statement

For every asymptotic homomorphism `φ_n` of `SL_4(Z)`, and all large `n`:
1. **Invariant.** `β_{ε,δ}` is well defined. It is `0` on homomorphisms, unchanged by
   pointwise `o(1)` perturbation on `F ∪ {M_1, M_2}`, and additive over direct sums.
   So `β_{ε,δ} ≠ 0` refutes matricial stability (and its padded form).
2. **Even central sector is dead.** `β_{+,+} = β_{−,+} = 0`.
3. **Odd central sector is antisymmetric.** `β_{+,−} = −β_{−,−}`.
4. **Refinement.** In the notation of the artifact, `β_ω(φ_n; g, M_1, M_2) = β_{ω,+} + β_{ω,−}`
   for `ω = ±1`. The same holds for `c`: `β_δ(φ_n; c, M_1, M_2) = β_{+,δ} + β_{−,δ}`.
   So the `g`-sector invariants satisfy `β_{+1}(g) = −β_{−1}(g)`, and both `c`-sector
   invariants vanish.
5. **Induced models carry nothing.** Let `N ⊴ SL_4(Z)` have finite index with `g ∉ N`,
   for instance any torsion-free congruence subgroup. Then every direct sum of
   `Ind_N^G ψ_n` with genuine representations has `β_{ε,δ} = 0` for all `ε, δ`.
6. **The constraint is sharp on the centralizer.** There is an asymptotic homomorphism `Θ_n`
   of `Δ' = Δ ⊔ hΔ = N_G(F)`, the stabilizer of `{g, cg}`, with `β_{+,−}(Θ_n) = −β_{−,−}(Θ_n) ≠ 0`.
   So parts 2–3 are the only restrictions visible on the normalizer, and the open problem
   is extension from `Δ'` to `SL_4(Z)`.

## Consequences

- **Where a witness must live.** If `SL_4(Z)` is refuted through this torus, the witness has
  a nonzero part on which `φ_n(−I) ≈ −1`. Compressing to the `c = −1` sector gives an
  asymptotic homomorphism with `φ_n(−I) → −1`. So no asymptotic homomorphism that factors
  through `PSL_4(Z)`, even approximately, can witness this class.
- **Two independent routes to the negation of `sl4z-matricially-stable`.**
  - Abstract: `sl4z-instability-from-delocalized-dadarlat`, through
    `weak-matricial-stability-kills-centralizer-even-cohomology`.
  - Explicit: `sl4z-instability-from-odd-sector-bott`, through the open
    `sl4z-odd-central-sector-bott-is-realizable`.

## Not claimed

- No asymptotic homomorphism of `SL_4(Z)` with some `β_{ε,δ} ≠ 0` is constructed.
- Whether parts 2–3 have analogues for the second involution `g_1` has not been worked out.
  Its Weyl element `k` also satisfies `k g_1 k^{-1} = −g_1`, so the same proof should apply.
