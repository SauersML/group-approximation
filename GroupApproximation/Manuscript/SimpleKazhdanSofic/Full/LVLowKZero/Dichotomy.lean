import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZero.Retraction

/-!
# `K₀ = 0` from the idempotent dichotomy

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Q2). Work order WO-LVLowK-1.

Let `R` carry a binary Leavitt family `(s₀, s₁, t₀, t₁)`. Suppose every idempotent `e` of `R`
is either `0` or Murray-von Neumann equivalent to `1`: there are `a, b` with `a b = e` and
`b a = 1`. In module terms, every cyclic projective module `R e` is `0` or `≅ R`. For
`R = L_k(1,2)` this is the statement `V(L(1,2)) = {0, [L]}` (Bergman, Trans. AMS 200 (1974),
Thm. 6.1; Ara-Goodearl-Pardo, K-Theory 26 (2002), Thm. 3.5).

* `idempotentAbsorbs_of_mul_eq_one`: if `a b = e` and `b a = 1`, then `e ⊕ 1 ∼ 1`, witnessed by
  `a t₀`, `s₀ b`, `t₁`, `s₁`;
* `idempotentAbsorbs_of_eq_zero_or`: both cases of the dichotomy absorb the unit;
* `algKZero_eq_zero_of_idempotent_dichotomy`: the dichotomy for all idempotents gives
  `K₀(R) = 0`, through `absorbsRegular_of_forall_idempotentAbsorbs` and
  `algKZero_eq_zero_of_forall_absorbsRegular`.
-/

namespace GroupApproximation.Full.LVLowKZero

open GroupApproximation.Full.LVLowK

universe u

variable {R : Type u} [Ring R]

/-- **An idempotent equivalent to `1` absorbs the unit.** If `a b = e` and `b a = 1`, then
`a t₀, s₀ b, t₁, s₁` witness `IdempotentAbsorbs e` (`simple_kazhdan_sofic_group.tex`
l.733-735). -/
theorem idempotentAbsorbs_of_mul_eq_one (L : LeavittFamily R) {e a b : R} (hab : a * b = e)
    (hba : b * a = 1) : IdempotentAbsorbs e := by
  have hbe : b * e = b := by
    rw [← hab, ← mul_assoc, hba, one_mul]
  refine ⟨a * L.t0, L.s0 * b, L.t1, L.s1, ?_, ?_, ?_, ?_, L.t1_s1, ?_⟩
  · rw [mul_assoc, ← mul_assoc L.t0, L.t0_s0, one_mul, hab]
  · rw [mul_assoc, hbe]
  · rw [← mul_assoc, L.t1_s0, zero_mul]
  · rw [mul_assoc, L.t0_s1, mul_zero]
  · rw [mul_assoc L.s0 b, ← mul_assoc b a, hba, one_mul, L.sum_range]

/-- Over a ring with a binary Leavitt family, the unit absorbs itself: `1 ⊕ 1 ∼ 1`. -/
theorem idempotentAbsorbs_one (L : LeavittFamily R) : IdempotentAbsorbs (1 : R) :=
  idempotentAbsorbs_of_mul_eq_one L (a := 1) (b := 1) (mul_one 1) (mul_one 1)

/-- Both alternatives of the idempotent dichotomy absorb the unit. -/
theorem idempotentAbsorbs_of_eq_zero_or (L : LeavittFamily R) {e : R}
    (h : e = 0 ∨ ∃ a b : R, a * b = e ∧ b * a = 1) : IdempotentAbsorbs e := by
  rcases h with h0 | ⟨a, b, hab, hba⟩
  · subst h0
    exact idempotentAbsorbs_zero
  · exact idempotentAbsorbs_of_mul_eq_one L hab hba

/-- **`K₀(R) = 0` from the idempotent dichotomy.** Over a ring with a binary Leavitt family, if
every idempotent is `0` or equivalent to `1`, then the algebraic `K₀(R)` is trivial
(`simple_kazhdan_sofic_group.tex` l.733-735, sec:questions Q2). -/
theorem algKZero_eq_zero_of_idempotent_dichotomy (L : LeavittFamily R)
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ ∃ a b : R, a * b = e ∧ b * a = 1)
    (z : AlgKZero R) : z = 0 :=
  algKZero_eq_zero_of_forall_absorbsRegular L
    (fun P => absorbsRegular_of_forall_idempotentAbsorbs L
      (fun e he => idempotentAbsorbs_of_eq_zero_or L (h e he)) P.carrier) z

end GroupApproximation.Full.LVLowKZero
