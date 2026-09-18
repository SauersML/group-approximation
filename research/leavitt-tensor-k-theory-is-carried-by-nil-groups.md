---
rg: 2
id: leavitt-tensor-k-theory-is-carried-by-nil-groups
kind: claim
title: For every algebra C, K_n(C ⊗ L(1,2)) is the image of NK_n(C ⊗ L(1,2)) under evaluation at 1, so K-regularity kills it, KH(C ⊗ L) = 0, and K(C) → K(C ⊗ L) is zero
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that proves K_*(L_2 ⊗ R) = 0 for regular supercoherent R through the Ara--Brustenga--Cortiñas sequence; this holds for every coefficient algebra C and shows that the only possible K-theory of C ⊗ L is a shadow of its Nil groups.
  prime-field-leavitt-tensor-powers-have-trivial-k-theory: that is K_1 = K_2 = 0 for tensor powers of L_p; this is a general reduction of such vanishing to K-regularity.
---

**ESTABLISHED** (lane proof by bh-free-26, 2026-09-18, elementary apart from standard facts on
Quillen `K`-theory; not independently reviewed). No priority is claimed. The homotopy-invariant
part (3) is presumably known through the `KH` form of the Ara--Brustenga--Cortiñas sequence.

## Statement

Let `k` be any commutative ring, `L = L_k(1,2)`, `C` any unital `k`-algebra, and
`R = C ⊗_k L`. Let `ev_0, ev_1 : R[t] → R` be evaluation, and `NK_n(R) = ker(ev_0)_*` on
`K_n(R[t])`. For every `n ∈ Z`:

1. **Nil carrier.** `(ev_1)_* : NK_n(R) → K_n(R)` is surjective. It has an explicit splitting
   `x ↦ Φ_*(x) - c_*(x)`, with `Φ` and `c` defined in the proof.
2. **K-regularity kills.** If `R` is `K_n`-regular (`NK_n(R) = 0`), then `K_n(R) = 0`.
3. **Homotopy `K`-theory.** `KH_n(R) = 0`.
4. **Absorption.**
   - The map `K_n(C) → K_n(C ⊗ L)`, induced by `c ↦ c ⊗ 1`, is zero.
   - Consequently `K_n(C ⊗ L^(⊗∞)) = 0`, where `L^(⊗∞) = colim_m L^(⊗m)`.

## Proof

**The doubling endomorphism.** Let `δ_L(x) = s_0 x t_0 + s_1 x t_1`, a unital endomorphism of
`L`, and `δ = id_C ⊗ δ_L`.
- With the row `V = (s_0, s_1)` and column `V' = (t_0, t_1)^T` (`VV' = 1`, `V'V = I_2`), we
  have `δ(x) = V diag(x,x) V'`. So `δ` is the diagonal `R → M_2(R)` followed by the ring
  isomorphism `Ad V`.
- Under Morita invariance the diagonal is `P ↦ P ⊕ P`, and `Ad V` is tensoring with a bimodule
  isomorphic to `R` (`V ⊗ r ↦ r`). Hence `δ_* = 2` on every `K_n(R)`.
- `δ(c ⊗ 1) = c ⊗ 1`.

**A polynomial path from the identity to `δ`.**
- *The swap unit.* `δ_L = ρ_u` for the digit-swap unit `u = Σ_(i,j) s_i s_j t_i t_j`, which
  maps the cone `[ji]` onto `[ij]`. Here `ρ_u(s_i) = u s_i` and `ρ_u(t_i) = t_i u^(-1)`.
  Directly, `u s_j = Σ_i s_i s_j t_i = δ_L(s_j)`, and `t_j u^(-1) = t_j u = δ_L(t_j)`.
- *Its matrix is elementary.* In depth-3 leaf coordinates `Θ : M_8(L) ≅ L`,
  `Θ(T) = Σ_(a,b) s_(w_a) T_(ab) t_(w_b)`, we get `u = Θ(P)`. Here `P` is the permutation
  matrix of `abc ↦ bac` on the eight words. That permutation is a product of two
  transpositions, so `P ∈ SL_8(Z) = E_8(Z)`.
- *The path.* Write `P = Π e_(ij)(m_l)` and put `U(t) = Θ(Π e_(ij)(t m_l)) ∈ (L ⊗ k[t])^x`.
  Then `U(0) = 1` and `U(1) = u`.
- *A family of endomorphisms.* For any unit `U` of `L[t] = L ⊗ k[t]`, the rule
  `s_i ↦ U s_i`, `t_i ↦ t_i U^(-1)` respects the Leavitt relations. So it defines a unital
  `φ : L → L[t]`, and `Φ = id_C ⊗ φ : R → R[t]` satisfies `ev_0 Φ = id` and `ev_1 Φ = δ`.

**Conclusion.** Let `c : R → R[t]` be the constant inclusion, and `x ∈ K_n(R)`.
- `Φ_* x = c_* x + ν(x)` with `ν(x) ∈ NK_n(R)`, because `(ev_0)_* Φ_* x = x`.
- Applying `(ev_1)_*` gives `2x = δ_* x = x + (ev_1)_* ν(x)`, so `x = (ev_1)_* ν(x)`. This
  is (1), and (2) follows.
- For `KH`, `(ev_0)_* = (ev_1)_*` on `KH(R[t]) ≅ KH(R)`, so `x = 2x` and `x = 0`. This is (3).
- For (4), `δ ∘ (c ↦ c ⊗ 1) = (c ↦ c ⊗ 1)` gives `ι_* = 2 ι_*`, so `ι_* = 0`. Apply this to
  `C ⊗ L^(⊗m)` in place of `C`. Every transition map `x ↦ x ⊗ 1` of the colimit is then zero
  on `K`-theory, and `K`-theory commutes with filtered colimits of rings. ∎

## Consequences

- **The ring gate of the master route becomes a regularity question.** Any finitely presented
  simple `F_p`-algebra `B` with centre `F_p` (for example a simple crossed product
  `C(X, F_p) ⋊ Λ`) has `K_1(B ⊗ L_p) = K_2(B ⊗ L_p) = 0` as soon as `B ⊗ L_p` is `K_1`- and
  `K_2`-regular. With `khanh-ara-cortinas-hypotheses-hold-for-leavitt-tensor-hosts` (master-route
  form), `(B ⊗ L_p)^x / F_p^x` is then finitely presented and simple. What remains open for
  such `B` is Nil-vanishing, not a `K`-theory computation.
- **Integral forms.** The proof works over `k = Z`, so it applies to `L_Z(1,2)` and to
  `Γ_Z`-type rings (`integral-counting-group-avoids-leavitt-linear-simple-hosts`). Their
  `K`-theory is carried by Nil groups, although the unit groups themselves are not simple.

## Lesson for general BH

Tensoring with `L` destroys every "honest" `K`-class. The doubling map `δ` multiplies
`K`-theory by 2, yet it is polynomially homotopic to the identity through elementary matrices,
because the swap unit is an even permutation. So the only way a Leavitt tensor host can fail
the `K_1 = K_2 = 0` gate is through Nil groups.

For Boone--Higman this turns the ring side of every Leavitt-tensor host construction (crossed
products, group algebras, Steinberg algebras) into one question: is `B ⊗ L` `K_1`- and
`K_2`-regular? That is the kind of statement Farrell--Jones-type theorems with coefficients
supply.
