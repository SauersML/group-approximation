---
rg: 2
id: z2-odd-commutator-below-half-forces-commuting-towers-proof
kind: route
title: The odd parts of a dimension-one tower system have |a| + |b| = 1, so a + ib has modulus at least 1/2 up to the commutator, and its polar part is a central odd unitary
target: z2-odd-commutator-below-half-forces-commuting-towers
requires:
  - ghs-z2-commuting-rokhlin-dimension-one-dual-sai
  - bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one
  - o2-central-sequence-k-theory-bi-cyclotomic-transfer
  - z2-o2-actions-anti-inner-and-o3-rokhlin-criterion
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
---

**Standard inputs, not re-read.**
- (LU) A unitary in `D_∞` lifts to unitaries in `D`.  If it is fixed by an
  automorphism `γ` of `D` of finite order, the lift can be taken in `D^γ`
  (average over the group and take polar parts for large `n`).
- (SEQ) Approximate relations along `ε_n → 0` become exact relations in `D_∞`.
- (KP) A unital Kirchberg algebra that is KK-contractible is `O_2`.

**Step 1: threshold.**  Let `(f_0, f_1, g_0, g_1)` be a tower system in `F`,
`a = f_0 − f_1` and `b = g_0 − g_1`.
- `f_0, f_1 ≥ 0` with `f_0 f_1 = 0`, so `|a| = f_0 + f_1 =: P`.  Likewise
  `|b| = g_0 + g_1 = 1 − P`.  So `0 ≤ P ≤ 1`, `a² = P²` and `b² = (1 − P)²`.
- Since `t² + (1 − t)² ≥ 1/2` on `[0, 1]`, `a² + b² ≥ 1/2`.
- With `x = a + ib`: `x*x = a² + b² + i[a, b]` and `xx* = a² + b² − i[a, b]`.  So both are
  `≥ 1/2 − ‖[a, b]‖ > 0` when `‖[a, b]‖ < 1/2`, and `x` is invertible.
- `β(a) = −a` and `β(b) = −b`, so `β(x) = −x`.  Then `x*x` is fixed, and so is `|x|`.
  `c = x|x|^(−1)` is a unitary in `F` with `β(c) = −c`.

**Step 2: duality.**
- *Odd unitary ⟹ commuting tower system.*  Write `c = a + ib` with `a, b`
  self-adjoint; both are odd.  `c` is normal, so `[a, b] = 0`, and `a² + b² = 1`.
  Put `f_0 = (a_+)²`, `f_1 = (a_−)²`, `g_0 = (b_+)²`, `g_1 = (b_−)²`.  Then
  `β(a_+) = (−a)_+ = a_−`, the sum is `a² + b² = 1`, the orthogonality relations
  hold, and all four elements commute.
- *Commuting ⟹ `‖[a, b]‖ < 1/2` ⟹ odd unitary.*  The first is trivial, the
  second is Step 1.
- *Odd unitary ⟺ `dim_Rok^c(β) ≤ 1`.*  By Corollary 3.27 of
  Gardella–Hirshberg–Santiago (`ghs-z2-commuting-rokhlin-dimension-one-dual-sai`),
  `dim_Rok^c(β) ≤ 1` iff there is a unital equivariant
  `(C(S^1), Lt) → (F, β)`, where `Lt` is rotation by `π`.  Such a map sends `z` to
  an odd unitary.  Conversely, an odd unitary `c` has `sp(c) = −sp(c)`, and
  `f ↦ f(c)` is unital and equivariant, since `β(f(c)) = f(−c)`.
- *Odd unitary ⟹ `β̂` SAI.*  `c ∈ F ⊆ D_∞ = ((D ⋊_β Z/2)_∞)^(β̂)`.  `Ad(c)` fixes
  `D` and sends `λ` to `c β(c*) λ = −λ = β̂(λ)`.  Lift `c` by (LU) to unitaries in
  `D = (D ⋊_β Z/2)^(β̂)`.
- *`β̂` SAI ⟹ odd unitary.*  Unitaries `v_n ∈ D` with `Ad(v_n) → β̂` give
  `v ∈ D_∞` commuting with `D`, with `vλv* = −λ`, that is, `β(v) = −v`.

**Step 3: `O_2`.**  Let `A = O_2` and `B = O_2 ⋊_α Z/2`.
- *`B` and `α̂`.*  By Step 1 of `o2-central-sequence-k-theory-bi-cyclotomic-transfer-proof`,
  `B` is a unital Kirchberg algebra and `α̂` is pointwise outer.  Theorem 2.3 of
  `bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one` gives towers for `α̂`
  along `ε_n → 0`, hence a tower system in `F_∞(B)` by (SEQ).  The same holds for
  `α` on `A`.
- *(a) SAI(α) ⟺ odd unitary for `α̂` in `F_∞(B)`.*  If `u ∈ (A_∞)^α` is a unitary
  with `Ad(u)|_A = σ`, then `w = u*λ` commutes with `A` (`u*σ(a)u = a`) and with
  `λ` (`λu*λ* = α(u*) = u*`), and `α̂(w) = −w`.  Conversely an odd unitary
  `w ∈ F_∞(B)` has the form `yλ` with `y ∈ A_∞`.  Commuting with `λ` gives
  `α(y) = y`, and commuting with `a` gives `y σ(a) y* = a`.  So `y*` is an invariant
  implementer; lift by (LU).  Step 2 with `β = α̂` gives the rest of (a).
- *(b) SAI(α̂) ⟹ Rokhlin.*  By Step 2 with `β = α`, SAI(α̂) gives
  `dim_Rok^c(α) ≤ 1`.  By Proposition 3.32 of Gardella–Hirshberg–Santiago, `α` is
  Rokhlin.  Item 1 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` makes
  `(O_2, α)` KK^G-contractible, so `B ≃_KK 0`, and (KP) gives `B ≅ O_2`.  By item 1
  of `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`, `2[1] = 0` in
  `K_0(F_∞(O_2)^α)` is equivalent to SAI(α̂).  By item 2 of
  `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`, Rokhlin gives
  `[1] = 0`.
- *(c)* is (a) for all outer `α`.
- *(d)*  If `B ≃_KK 0`, detection at `2` for `α` says `α` is Rokhlin (item 3 of
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`).  Rokhlin gives
  `dim_Rok^c(α) = 0`.  Conversely `dim_Rok^c(α) ≤ 1` gives Rokhlin by
  Proposition 3.32.  Step 2 with `β = α` turns this into the commutator bound.

**Model test for the threshold.**  The faithful quasi-free `γ : Z_2 ↷ O_∞` has
Rokhlin dimension `1` (Barlak–Enders–Matui–Szabó–Winter, Corollary 2.2).  By
the abstract of Hirshberg–Phillips, arXiv:1410.6581, no nontrivial finite group
acts on `O_∞` with finite commuting-tower Rokhlin dimension.  So by Step 2 every
tower system for `γ` has `‖[a, b]‖ ≥ 1/2`: the bound is never beaten there, as
it must not be.
