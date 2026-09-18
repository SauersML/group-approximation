import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGen
import GroupApproximation.Meta.AxiomGuard

/-!
# Subgroups of `St_k(ℤ[1/n])` containing the standard generators (lane `bh-met-93s`, part 3)

`czK2FngGtOneRank3_eq_top`: for `k ≥ 3`, a subgroup of `St_k(ℤ[1/n])` that contains every
`x_ij(1)` and every `x_ij(1/n)` is the whole group.  This is the proof of
`czK2Fng_steinbergAway_fg`, with the generated subgroup replaced by an arbitrary subgroup.
The coefficients `a` with every `x_ij(a)` in the subgroup form a subring (root additivity, and
multiplication through the commutator via a third index).  That subring contains `1/n`, hence
every `c · (1/n)^e`, hence everything (`IsLocalization.Away.surj`).

Proved outright.  There are no hypotheses and no literature inputs.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- **Generation.**  For `k ≥ 3`, a subgroup of `St_k(ℤ[1/n])` containing all `x_ij(1)` and all
`x_ij(1/n)` is `⊤`. -/
theorem czK2FngGtOneRank3_eq_top (n k : ℕ) (hk : 2 < k)
    (H : Subgroup (SteinbergGroup (Fin k) (Localization.Away (n : ℤ))))
    (h1 : ∀ (i j : Fin k) (h : i ≠ j), x i j h 1 ∈ H)
    (hu : ∀ (i j : Fin k) (h : i ≠ j),
      x i j h (IsLocalization.Away.invSelf (n : ℤ) : Localization.Away (n : ℤ)) ∈ H) :
    H = ⊤ := by
  classical
  have hu1 : algebraMap ℤ (Localization.Away (n : ℤ)) (n : ℤ) *
      (IsLocalization.Away.invSelf (n : ℤ) : Localization.Away (n : ℤ)) = 1 :=
    IsLocalization.Away.mul_invSelf (n : ℤ)
  let C : Subring (Localization.Away (n : ℤ)) :=
    { carrier := {a | ∀ (i j : Fin k) (h : i ≠ j), x i j h a ∈ H}
      mul_mem' := by
        intro a b ha hb i j hij
        obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hk
        have hil : i ≠ l := hli.symm
        have hc : ⁅x i l hil a, x l j hlj b⁆ ∈ H := by
          rw [commutatorElement_def]
          exact H.mul_mem
            (H.mul_mem (H.mul_mem (ha i l hil) (hb l j hlj)) (H.inv_mem (ha i l hil)))
            (H.inv_mem (hb l j hlj))
        rw [x_commutator i l j hil hlj hij] at hc
        exact hc
      one_mem' := by
        intro i j hij
        exact h1 i j hij
      add_mem' := by
        intro a b ha hb i j hij
        rw [← x_mul]
        exact H.mul_mem (ha i j hij) (hb i j hij)
      zero_mem' := by
        intro i j hij
        rw [x_zero]
        exact H.one_mem
      neg_mem' := by
        intro a ha i j hij
        rw [x_neg]
        exact H.inv_mem (ha i j hij) }
  have huC : (IsLocalization.Away.invSelf (n : ℤ) : Localization.Away (n : ℤ)) ∈ C := by
    intro i j hij
    exact hu i j hij
  have hC : ∀ z : Localization.Away (n : ℤ), z ∈ C := by
    intro z
    obtain ⟨e, c, hc⟩ := IsLocalization.Away.surj (n : ℤ) z
    have hz : z = algebraMap ℤ (Localization.Away (n : ℤ)) c *
        (IsLocalization.Away.invSelf (n : ℤ) : Localization.Away (n : ℤ)) ^ e := by
      rw [← hc, mul_assoc, ← mul_pow, hu1, one_pow, mul_one]
    rw [hz, eq_intCast (algebraMap ℤ (Localization.Away (n : ℤ))) c]
    exact C.mul_mem (intCast_mem C c) (pow_mem huC e)
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by
    (relations (I := Fin k) (R := Localization.Away (n : ℤ))) H ?_ g
  rintro ⟨i, j, hij, a⟩
  change x i j hij a ∈ H
  exact hC a i j hij

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_eq_top

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
