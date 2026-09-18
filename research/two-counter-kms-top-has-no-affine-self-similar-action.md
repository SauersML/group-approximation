---
rg: 2
id: two-counter-kms-top-has-no-affine-self-similar-action
kind: claim
title: For K >= 2 the KMS top factor R_K semidirect U_K has no faithful self-similar affine action with its lamps as translations, on any p^d-ary tree and with arbitrary non-Toeplitz corners
distinct_from:
  affine-self-similar-groups-are-function-field-linear: that treats block-Toeplitz affine maps over F_p[[X]]^d, where a section keeps its parent's linear part; this allows arbitrary causal linear maps, whose sections have new linear parts (corners), including infinite-state ones.
  kms-configuration-modules-have-trivial-coinvariants: that excludes the lamp-digit shape for the configuration module T; this excludes the affine shape for the multi-counter top factor B_0.
---

**ESTABLISHED** by the proof below (lane bh-free-25, 2026-09-18; elementary, not
reviewed).

## Setting

- `R = R_K = F_p[s_i^{±1}, (1 − s_i)^{-1} : i ≤ K]`, a normal Noetherian domain of Krull
  dimension `K`.
- `U = U_K = ⟨s_i, 1 − s_i⟩ ≤ R^×`, free abelian of rank `2K`.
- `B = R ⋊ U`. By G4 of KMS and item 1 of What is known in
  `kms-configuration-modules-carry-self-similar-structures`, this is the top factor `B_0`,
  since `⟨t, (t^{-1} − 1)⟩ = ⟨t, 1 − t⟩`.
- An **affine realization** is a faithful action of `B` on the `p^d`-ary tree with
  boundary `(F_p^d)^ℕ` such that:
  - each `r ∈ R` acts by translation by a sequence `Φ(r)`;
  - each `u ∈ U` acts by a causal (block lower-triangular) invertible `F_p`-linear map
    `L_u`;
  - the set of all these affine maps is closed under sections.

  Toeplitz or not, finite-state or not, every realization of the kind "2×2 matrices" or
  "linear transducer on digit blocks" is of this form.

## Statement

If `K ≥ 2`, then `B` has no affine realization, for any `p` and `d`. For `K = 1` it has one
(the affine action on `F_p[[X]]`, `p` odd).

## Proof

**Step 1: the data.**
- The section of a translation is translation by the shifted sequence. That section lies
  in `Φ(R)`, so `shift ∘ Φ = Φ ∘ σ` for a unique additive `σ: R → R`.
- Put `λ(m) = Φ(m)_0 ∈ F_p^d`. Then `Φ(m) = (λσ^n m)_{n≥0}`.
- The section of `L_u` at a letter `v` is `x' ↦ L_u^{(1)}x' + C_u v`, where `L_u^{(1)}` is
  the corner. Being in the group forces `L_u^{(1)} = L_{ψ(u)}` for a unique `ψ(u) ∈ U`, and
  `C_u v = Φ(c_u(v))`. The corner map is multiplicative, so `ψ` is an endomorphism.
- Comparing first blocks and tails of `Φ(um) = L_uΦ(m)` gives
  - `λ(um) = χ(u)λ(m)`, with `χ(u) = (L_u)_{00}`;
  - `σ(um) = ψ(u)σ(m) + c_u(λ(m))`.

**Step 2: `J = ker λ` is a nonzero ideal on which `σ` is semilinear.**
- `J` is `U`-invariant, and `R` is spanned by `U`, so `J` is an ideal. Its codimension is
  at most `d`, so `J ≠ 0`.
- For `m ∈ J`, `σ(um) = ψ(u)σ(m)`.
- If `m ∈ J` and `σ(m) = 0`, then every digit of `m` vanishes, so `m = 0`. Hence `σ` is
  injective on `J`, and `σ(J) ≠ 0`.
- If `Σ a_u u = 0` in `R`, then `Σ a_u ψ(u)` kills `σ(J)`, so it is `0` because `R` is a
  domain. So `ψ` extends to a ring endomorphism `ψ̃` of `R`, and `σ(rm) = ψ̃(r)σ(m)` for
  `r ∈ R` and `m ∈ J`.
- If `ψ̃(r) = 0`, then `σ(rJ) = 0`, so `rJ = 0` and `r = 0`. Hence `ψ̃` is injective.
- For `j, j' ∈ J`, `ψ̃(j)σ(j') = σ(jj') = ψ̃(j')σ(j)`. So `σ|_J = g·ψ̃|_J` for one
  `g ∈ Frac R`.

**Step 3: `ψ̃` is a product of one-variable maps (unit lemma).**
- *Lemma.* If `u ∈ U` and `1 − u ∈ U`, then `u ∈ F_p(s_i) \ F_p` for a single `i`.
- *Proof of the lemma.*
  - Write `u = ∏ s_i^{a_i}(1 − s_i)^{b_i}` and `1 − u = ∏ s_i^{c_i}(1 − s_i)^{d_i}`, and use
    the valuation `v` of `s_1 = 0`.
  - If `a_1 > 0`, then `1 − u ≡ 1` there. Reducing `1 − u` modulo `s_1` gives
    `∏_{i≥2} s_i^{c_i}(1 − s_i)^{d_i} = 1`, so `1 − u ∈ F_p(s_1)`.
  - If `a_1 < 0`, apply the same argument to `u^{-1} − 1 = (1 − u)/u`. (Its residue is
    `−1`, so for `p` odd this case cannot occur at all.)
  - If `a_1 = 0`, use `1 − s_1` in the same way.
  - So `u` involves `s_i` only if `u ∈ F_p(s_i)`. A `u` involving two variables would lie
    in `F_p(s_1) ∩ F_p(s_2) = F_p`, while `U ∩ F_p = {1}` and `1 − 1 ∉ U`.
- Now `ψ̃(s_i)` and `1 − ψ̃(s_i) = ψ̃(1 − s_i)` lie in `U`. So `ψ̃(s_i) = f_i(s_{π(i)})`
  with `f_i` a nonconstant rational function.
- `ψ̃` is injective, so the transcendence degree forces `π` to be a bijection. Each
  coordinate map is finite on the affine line, so `ψ̃^*` has finite fibres.

**Step 4: `g ∈ R` (this is where `K ≥ 2` enters).**
- Suppose `ψ̃(J) ⊆ 𝔭` for a height-one prime `𝔭`. Then `ψ̃^{-1}(𝔭)` is a prime containing
  the finite-codimension ideal `J`, so it is maximal. So `ψ̃^*` contracts the curve
  `V(𝔭)` to one point, contradicting finite fibres.
- So the ideal `ψ̃(J)R` lies in no height-one prime. In a normal Noetherian domain its
  inverse is `R`. As `g·ψ̃(J) ⊆ R`, we get `g ∈ R`.

**Step 5: a nonzero ideal with no digits.**
- `J ⊇ 𝔞 = ∏_{i≤r} 𝔪_{Q_i}^N` for some closed points `Q_i` and some `N`.
- `ψ̃^*` maps closed points to closed points without raising residue degree. So the
  forward orbit `S` of `{Q_i}` is finite. Put `𝔟 = ∏_{Q∈S} 𝔪_Q^N ⊆ 𝔞 ⊆ J`.
- For `Q ∈ S`, `ψ̃(𝔪_{ψ̃^*Q}) ⊆ 𝔪_Q`, and `ψ̃^*Q ∈ S`. So `ψ̃(𝔟) ⊆ 𝔟`, and
  `σ(𝔟) = gψ̃(𝔟) ⊆ 𝔟`.
- Also `λ(𝔟) = 0`. So every digit of every element of `𝔟` is `0`, and `Φ(𝔟) = 0`.
- But `𝔟 ≠ 0` and `Φ` is injective. Contradiction. ∎

**Why `K = 1` escapes.** There `ψ̃(J)` can lie in a height-one prime, which is maximal,
and `g` may have a pole. With `ψ̃ = id`, `J = (s − c)` and `g = 1/(s − c)`, this is
`D(f) = (f − f(0))/X`.

## Consequence

A self-similar realization of the multi-counter KMS top, and so of any hard KMS group
containing it, must be nonlinear on digits: carries that do not come from `F_p`-linear
maps (odometer additions with carry, or Nekrashevych-type germs). No choice of matrices
or linear transducers works.
