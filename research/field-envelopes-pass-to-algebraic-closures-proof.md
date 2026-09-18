---
rg: 2
id: field-envelopes-pass-to-algebraic-closures-proof
kind: route
title: Compatible regular representations put an algebraic closure in the ultramatricial part of a Leavitt algebra
target: field-envelopes-pass-to-algebraic-closures
requires:
  - fp-simple-q-algebras-embed-in-fp-simple-rings
  - rational-function-fields-embed-in-fp-simple-rings
  - leavitt-nekrashevych-completion-simplicity-criterion
---

Lane proof, not independently reviewed. Write `L_F = L_F(1,2)` for a field `F`.

## 1. The host R ⊗_Q L_Q is finitely presented and simple
`R` contains `K`, which has characteristic zero, so `R` is a `Q`-algebra by
`fp-simple-q-algebras-embed-in-fp-simple-rings`, part 3.
- `L_Q` is simple with centre `Q`, by part 4 of
  `leavitt-nekrashevych-completion-simplicity-criterion`. So
  `R ⊗_Q L_Q` is simple by the tensor lemma of
  `polynomially-representable-envelopes-via-leavitt-tensors`, §2.
- `R ⊗_Q L_Q = R ⊗_Z L_Z(1,2)` because `R` is a `Q`-algebra. So it is presented by the two
  presentations together with commutation of the two generating sets, which is finite.
- Tensoring over the field `Q` preserves injectivity, so
  `L_K = K ⊗_Q L_Q -> R ⊗_Q L_Q` is injective. It is unital when `K ⊆ R` is unital.

## 2. Matrix absorption in L_F, compatibly
- `L_F ≅ L_F^2` as right modules, hence `L_F ≅ L_F^r` for every `r >= 1`, by induction.
  So there is a unital `F`-algebra isomorphism `θ_r : L_F -> M_r(L_F)`.
- Let `d_1 | d_2 | ...` with `r_i = d_(i+1)/d_i`. Define unital isomorphisms
  `φ_i : L_F -> M_(d_i)(L_F)` by `φ_1 = θ_(d_1)` and `φ_(i+1) = M_(d_i)(θ_(r_i)) ∘ φ_i`,
  identifying `M_(d_i)(M_(r_i)(L_F)) = M_(d_(i+1))(L_F)` by blocks.
- Put `ι_i(x) = φ_i^(-1)(x·1)` for `x ∈ M_(d_i)(F)`. It is a unital injective map
  `M_(d_i)(F) -> L_F`.
- **Compatibility.** Let `κ_i(x) = x ⊗ I_(r_i)` be the block Kronecker map, whose
  `(a,b)` block is `x_(ab) I_(r_i)`. Since `θ_r` is unital and `F`-linear,
  `M_(d_i)(θ_(r_i))^(-1)` sends that block matrix to `(x_(ab)·1)_(ab)`. So
  `ι_(i+1) ∘ κ_i = ι_i`.

## 3. Algebraic extensions
Let `E ⊇ F` be a countable algebraic extension, a union of finite extensions
`F = E_0 ⊆ E_1 ⊆ E_2 ⊆ ...`, and let `d_i = [E_i : F]`.
- Start from `E_0 = F`, `d_0 = 1`. Choose `F`-bases compatibly: a basis of `E_(i+1)` over
  `F` consists of the products `b c`, with `b` running over the basis of `E_i` and `c` over
  an `E_i`-basis of `E_(i+1)`, ordered with the `E_i`-index `b` outer, as in `κ_i`.
- With these bases, the regular representation `ρ_(i+1)` of `E_(i+1)` restricts on `E_i`
  to `κ_i ∘ ρ_i`.
- So `α ↦ ι_i(ρ_i(α))` for `α ∈ E_i` is a well-defined unital injective ring
  homomorphism `E -> L_F`.
- With `F = K` and `E = K̄`, which is countable because `K ⊆ R` is countable, part 1
  follows from §1.

## 4. Finite transcendence degree
Let `E` be countable of characteristic zero, with a transcendence basis `t_1..t_k`.
- `E` is algebraic over `F_k = Q(t_1..t_k)`. By
  `rational-function-fields-embed-in-fp-simple-rings`, `F_k` embeds unitally in `R_k`, or
  `F_0 = Q ⊆ R_L`.
- So `E` embeds unitally in `R_k ⊗_Q L_Q`, by §§1–3.
- For `k = 0`, `L_Q` already lies in `R_L`: the Leavitt family of `R_L` gives a unital
  `Q`-algebra map `L_Q -> R_L`, which is injective because `L_Q` is simple. Hence
  `Q̄ ⊆ L_Q ⊆ R_L`.
- Matrix rings: `M_n(E) ⊆ M_n(L_F) ≅ L_F`. ∎
