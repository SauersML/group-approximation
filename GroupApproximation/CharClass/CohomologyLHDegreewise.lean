import GroupApproximation.CharClass.LerayHirschColumnPack

/-!
# Reading a Leray–Hirsch instance degreewise

`LerayHirschGraded` is indexed by the computed cardinal `lhDomainCard r n`, which
equals the rank in the degrees where every summand survives but is **not**
definitionally equal to it, since `n / 2` does not reduce for a variable `n`.  The
index sits inside the type of each coefficient, so reading the instance at a fixed
index type is a dependent transport rather than a rewrite.

This file is that transport.  `cc-thom`'s Thom datum consumes the coefficients at
`Fin (r + 1)` in degree `2 * r`, where the cardinal is `r + 1`; the general form
takes the equality as a hypothesis so the same lemma serves any degree in which
the two agree.

Nothing here is a new mathematical statement: the transport carries the
Leray–Hirsch combination to the same combination reindexed, so bijectivity moves
across unchanged.

## Main declarations

* `LHCast.lhIndexEquiv` — the index equivalence, `Fin (lhDomainCard r n) ≃ Fin r`.
* `LHCast.lhDomainEquiv` — the coefficient transport, as a linear equivalence.
* `LHCast.lhMap_eq_sum_lhTerm` — it carries `lhMap` to the reindexed combination.
* `LHCast.bijective_sum_lhTerm_of_graded` — **the degreewise reading**.
* `LHCast.bijective_sum_lhTerm_top` — the shape `cc-thom` consumes.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-! ## 1. The index equivalence -/

/-- Where the cardinal equals the rank, the two index sets agree, and the
identification is the identity on underlying naturals. -/
def lhIndexEquiv (r n : ℕ) (h : lhDomainCard r n = r) : Fin (lhDomainCard r n) ≃ Fin r where
  toFun i := ⟨(i : ℕ), lt_rank_of_lhDomain i⟩
  invFun i := ⟨(i : ℕ), by rw [h]; exact i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## 2. The coefficient transport -/

/-- **The dependent transport**, as a linear equivalence.  The index sits inside
the type of each coefficient, so this is not a rewrite; but the identification is
the identity on underlying naturals, so every field is `rfl`. -/
def lhDomainEquiv (X : TopCat.{0}) (r n : ℕ) (h : lhDomainCard r n = r) :
    ((i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ)))
      ≃ₗ[ZMod 2] ((i : Fin r) → Hmod2 X (n - 2 * (i : ℕ))) where
  toFun a i := a ((lhIndexEquiv r n h).symm i)
  invFun b i := b (lhIndexEquiv r n h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv a := by funext i; rfl
  right_inv b := by funext i; rfl

/-! ## 3. The transport carries the combination -/

set_option maxHeartbeats 1000000 in
/-- **The combination is the same after reindexing.**  Every summand of `lhMap`
is a `lhTerm` at an index the degree admits, so no summand is created or lost. -/
theorem lhMap_eq_sum_lhTerm (π : P ⟶ X) (ξ : Hmod2 P 2) (r n : ℕ)
    (h : lhDomainCard r n = r)
    (a : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    lhMap π ξ r n a
      = ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (lhDomainEquiv X r n h a i) := by
  simp only [lhMap]
  refine Fintype.sum_equiv (lhIndexEquiv r n h) _ _ (fun i => ?_)
  exact (lhTerm_of_le π ξ (two_mul_le_of_lhDomain i) (a i)).symm

/-! ## 4. The degreewise reading -/

set_option maxHeartbeats 1000000 in
/-- **A Leray–Hirsch instance, read at the rank instead of at the cardinal.**  In
any degree where the two agree, the coefficients form a free family indexed by
`Fin r`. -/
theorem bijective_sum_lhTerm_of_graded {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) (n : ℕ) (h : lhDomainCard r n = r) :
    Function.Bijective (fun a : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (a i)) := by
  have hfun : (fun a : (i : Fin r) → Hmod2 X (n - 2 * (i : ℕ)) =>
      ∑ i : Fin r, lhTerm π ξ n (i : ℕ) (a i))
      = (lhMap π ξ r n) ∘ (lhDomainEquiv X r n h).symm := by
    funext a
    have hb := lhMap_eq_sum_lhTerm π ξ r n h ((lhDomainEquiv X r n h).symm a)
    rw [(lhDomainEquiv X r n h).apply_symm_apply] at hb
    exact hb.symm
  rw [hfun]
  exact (L.bij n).comp (lhDomainEquiv X r n h).symm.bijective

/-! ## 5. The top degree, which is what the Thom datum consumes -/

/-- At degree `2 * r` a rank-`(r+1)` instance has every summand. -/
theorem lhDomainCard_succ_two_mul (r : ℕ) : lhDomainCard (r + 1) (2 * r) = r + 1 := by
  unfold lhDomainCard
  omega

/-- **The shape `cc-thom`'s Thom datum consumes**: the coefficients of a rank-`(r+1)`
instance in degree `2 * r`, indexed by `Fin (r + 1)`, with the top coefficient
group at the rank. -/
theorem bijective_sum_lhTerm_top {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ (r + 1)) :
    Function.Bijective (fun a : (i : Fin (r + 1)) → Hmod2 X (2 * r - 2 * (i : ℕ)) =>
      ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)) :=
  bijective_sum_lhTerm_of_graded L (2 * r) (lhDomainCard_succ_two_mul r)

end LHCast

end

end GroupApproximation.CharClass
