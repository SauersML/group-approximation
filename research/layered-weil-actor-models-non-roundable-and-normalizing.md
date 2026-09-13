---
rg: 2
id: layered-weil-actor-models-non-roundable-and-normalizing
kind: claim
title: At the one-compressor affine symplectic pair, layered Schrödinger--Weil models are totally non-roundable on the vertex and normalize the vertex commutant
distinct_from:
  rf-kazhdan-group-not-flexibly-hs-stable: that gives one non-roundable asymptotic representation of the vertex Z^2g x| Sp_2g(Z) alone; this extends a layered family of them to a trace-preserving model of an ascending HNN actor, and proves total non-roundability and normalization of the commutant.
  one-compressor-actor-models-with-exact-origin-vertex: that layers genuine origin-type representations along a Kun--Thom compressor, so the vertex is exact and the commutant not normalized; this layers projective Schrödinger--Weil representations along a symplectic compressor, so the vertex is totally non-roundable and the commutant normalized.
  kt-actor-model-with-totally-non-roundable-vertex: that is the open existence question at the Theorem E pair; this realizes a normalizing witness at a different infranormal pair and records what that pair has and the Theorem E pair lacks.
artifacts:
  - research/artifacts/ex2-ft-layered-weil-calibration-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `g >= 2`, `p` a prime, `Γ = Z^(2g) ⋊ Sp_(2g)(Z)`, `φ(v,A) = (pv, A)`.
- `V = Γ *_φ ≅ Z[1/p]^(2g) ⋊ (Sp_(2g)(Z) × <t>)`.
- `tΓt^(-1) = pZ^(2g) ⋊ Sp_(2g)(Z)` is a proper subgroup of `Γ`, so the pair is infranormal and non-normal.
- `Γ` is residually finite and Kazhdan. `V` is not Kazhdan.

**Construction.** Take primes `ℓ ∤ 6p`, `L = ⌊log ℓ / 4 log p⌋` and `c_j = p^(2j)` for `j < L`.
- `S~_c` is the Schrödinger--Weil representation of `(Heisenberg cover of Γ) mod ℓ` with central character
  `e(c/ℓ)`.
- `σ_ℓ(γ) = ⊕_(j<L) S~_(c_j)(s(γ))`.
- `σ_ℓ(t)` shifts layer `j+1` to layer `j` through the intertwiner of `S~_(c_j)∘φ~` with `S~_(p^2 c_j)`, and
  wraps layer 0 to layer `L-1`.

**Theorem.** `σ = (σ_ℓ)_U` is a trace-preserving homomorphism `V -> U(prod_U M_(Lℓ^g))`, and:
1. **Total non-roundability.** `σ|Γ` is totally non-roundable. No nonzero projection of `R = σ(Γ)' ∩ M` is
   roundable, and `d(σ) >= κ` for every Kazhdan pair `(F_Γ, κ)`.
2. **Normalization.** `R = prod_U ℓ^∞(L_ℓ)` is the diffuse layer algebra, `σ(V)` normalizes it, and
   `R = σ(N_V)' ∩ M` with `N_V = <<Γ>>_V`.

**Reading.**
- **Pointwise separation.** Total non-roundability of the vertex and normalization of its commutant coexist at
  an explicit infranormal, non-normal pair with a residually finite Kazhdan vertex. So "(H1) fails at `σ`"
  never implies "`σ` does not normalize" at this generality.
  - This is the first, normalizing kind of witness in `kt-actor-model-with-totally-non-roundable-vertex`.
  - It does not extend to the coset wreath over `V/Γ`.
- **What it spends.** Both ingredients are absent at the Theorem E pair.
  - **A rational degree-two class on the vertex**, the Heisenberg class. The Kun--Thom vertex has `H_2` finite
    in the stable range.
  - **Følner layers along a `Z` quotient of the actor.** The Theorem E actor is Kazhdan.
- **Contrast.** The Kun--Thom one-compressor models layer genuine origin-type representations: exact vertex,
  non-normalized commutant. These layer projective representations: non-roundable vertex, normalized commutant.
- **Model test.** With every `c_j = 0` the layers are genuine representations of `Γ`, and the vertex rounds.

Derivation: `layered-weil-actor-models-non-roundable-and-normalizing-proof`.
