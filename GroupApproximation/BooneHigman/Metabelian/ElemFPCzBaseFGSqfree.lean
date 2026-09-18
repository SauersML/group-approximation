import GroupApproximation.BooneHigman.Metabelian.ElemFPBaseFGCzStep
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroRankFourFPReduce
import Mathlib.Algebra.Squarefree.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `BaseFG` from rank-four normal generation at squarefree `m` (lane `bh-met-95`)

Target: `CharZeroK2BaseFGStatement` (module `ElemFPCharZeroK2Split`, line 100), i.e.
`K₂(N, ℤ[1/m])` is finitely generated for every `m` and every `N ≥ 5`.  It is **not** closed
here.  An unconditional proof needs the arithmetic of `ℤ[1/m]` at rank four (Behr's finite
presentation of `SL_4(ℤ[1/m])`, or Tate's computation of `K₂`), which the corpus does not
have.  The `F_p[t]` normal-form and Euclid machinery (`k2PolyNF_*`, `k2PolyEuclid_*`) is stated
only for `Polynomial (ZMod p)`.  It proves `K₂ = 1` there by a stabiliser normal form, which
cannot hold over `ℤ[1/m]`, since `{-1, -1} ≠ 1` already sits in a rank-two subgroup.

## The residual

`czBaseFG_SqfreeFourStatement`: for every **squarefree** `m > 1`, `K₂(4, ℤ[1/m])` is finitely
normally generated in `St_4(ℤ[1/m])`.

## Proved here

* `czBaseFG_fiveFG_of_fngFour`: for a single `m > 0`, normal generation of `K₂(4)` gives finite
  generation of `K₂(5)`.  This uses the proved surjective stability `4 → 5`
  (`czStabGen_k2SurjStab_of_triOff czTriOff_triOffStatement`) and the fact that stabilised
  `K₂` is central.
* `czBaseFG_fiveFG_of_sqfreeFour`: strong induction on `n`.  The case `n = 1` is
  `czBaseFGCz_fg_five_one` (from P13).  A squarefree `n > 1` is the residual.  A non-squarefree
  `n` has `x * x ∣ n` with `x ≥ 2`, so `n = c * x` with `x ∣ c`, and then
  `ℤ[1/c] ≅ ℤ[1/(cx)]` (`czBaseFGCz_fg_of_dvd`).
* `czBaseFG_baseFG_of_sqfreeFour`: the target, using ranks `N ≥ 6` (`czBaseFGCz_fg_ge_five`)
  and `m = 0` (`charZeroK2BaseFG_of_pos`).
* `czBaseFG_sqfreeFour_of_rankFour`, `czBaseFG_sqfreeFour_of_rankThree`,
  `czBaseFG_sqfreeFour_of_slFour`: the three existing rank-≤4 leaves each imply the residual.
  These are `CZK2FngRankFourStatement`, `czK2FngGtOne_RankThreeStatement` and
  `czRankFourFP_SLFourStatement` (Z3).

## Strength (LOUD)

* It is **not** logically weaker than the target.  `BaseFG ⇒ residual` would need normal
  generation at rank 4 from finite generation at rank 5, i.e. injective stability
  `K₂(4) → K₂(5)` or a finite presentation of `E_4(ℤ[1/m])`.  Neither is in the corpus.  In
  the corpus the two are **incomparable**, and only `residual ⇒ BaseFG` is proved.
* It is implied by `CZK2FngRankFourStatement` and by everything above it (Z3, RankThree, the
  one-prime step, Z4).  It differs from `CZK2FngRankFourStatement` **only** by dropping the
  non-squarefree `m`.  Those cases follow from the squarefree ones through
  `ℤ[1/m] ≅ ℤ[1/rad m]`.
  So the gain is a strictly smaller set of instances, not a new idea: essentially a
  restatement of the rank-four leaf.  **All the depth of Behr's rank-four finite presentation
  remains.**

## Truth check

True.  For `m > 1`, `SL_4(ℤ[1/m])` is finitely presented (Behr; Borel–Serre), and
`SL_4 = E_4` over `ℤ[1/m]` (`czRankFourFP_slEquiv`).  With `St_4(ℤ[1/m])` finitely generated
(`czK2Fng_steinbergAway_fg`), the kernel `K₂(4, ℤ[1/m])` is then finitely normally generated.
These citations are truth checks only and are not hypotheses anywhere.  The unit-symbol route
is not used; it is false (for `m = 5` the unit symbols miss half of `F₅^×`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **The residual (lane `bh-met-95`).**  For every squarefree `m > 1`, `K₂(4, ℤ[1/m])` is
finitely normally generated.  True (Behr, truth check only), and implied by
`CZK2FngRankFourStatement` (`czBaseFG_sqfreeFour_of_rankFour`).  It is **not** implied by the
target in the corpus; see the module docstring. -/
def czBaseFG_SqfreeFourStatement : Prop :=
  ∀ m : ℕ, 1 < m → Squarefree m →
    (K2 (Fin 4) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_SqfreeFourStatement

/-- **Per-`m` rank lift.**  If `K₂(4, ℤ[1/m])` is finitely normally generated, then
`K₂(5, ℤ[1/m])` is finitely generated.  This uses the proved surjective stability `4 → 5`. -/
theorem czBaseFG_fiveFG_of_fngFour {m : ℕ} (hm : 0 < m)
    (h4 : (K2 (Fin 4) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated) :
    Group.FG (K2 (Fin 5) (Localization.Away (m : ℤ))) :=
  czBaseFGCz_fg_succ_of_fng_of_le_map (n := 4) h4
    (czStabGen_k2SurjStab_of_triOff czTriOff_triOffStatement m 4 hm le_rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_fiveFG_of_fngFour

/-- **Squarefree reduction at rank 5.**  The residual gives finite generation of
`K₂(5, ℤ[1/n])` for every `n > 0`.  The proof is strong induction on `n`.  A non-squarefree
`n` is written as `n = c * x` with `x ≥ 2` and `x ∣ c`, and then `ℤ[1/c] ≅ ℤ[1/(cx)]`. -/
theorem czBaseFG_fiveFG_of_sqfreeFour (h : czBaseFG_SqfreeFourStatement) :
    ∀ n : ℕ, 0 < n → Group.FG (K2 (Fin 5) (Localization.Away (n : ℤ))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      exact czBaseFGCz_fg_five_one
    · by_cases hsq : Squarefree n
      · exact czBaseFG_fiveFG_of_fngFour hn (h n (by omega) hsq)
      · obtain ⟨x, ⟨k, hk⟩, hx⟩ : ∃ x : ℕ, x * x ∣ n ∧ ¬IsUnit x := by
          by_contra hne
          exact hsq fun x hxn ↦ Classical.byContradiction fun hu ↦ hne ⟨x, hxn, hu⟩
        obtain ⟨c, rfl⟩ : ∃ c : ℕ, n = c * x :=
          ⟨x * k, hk.trans (Nat.mul_right_comm x x k)⟩
        have hxpos : 0 < x := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hn
        have hcpos : 0 < c := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hn
        have hx1 : x ≠ 1 := fun he ↦ hx (by rw [he]; exact isUnit_one)
        have hclt : c < c * x := (lt_mul_iff_one_lt_right hcpos).mpr (by omega)
        have hcx : c = x * k :=
          Nat.eq_of_mul_eq_mul_right hxpos (hk.trans (Nat.mul_right_comm x x k))
        exact czBaseFGCz_fg_of_dvd hcpos hxpos ⟨k, hcx⟩ (ih c hclt hcpos)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_fiveFG_of_sqfreeFour

/-- The residual gives `CharZeroK2BasePosFGStatement`. -/
theorem czBaseFG_basePos_of_sqfreeFour (h : czBaseFG_SqfreeFourStatement) :
    CharZeroK2BasePosFGStatement :=
  fun m N hm h5N ↦ czBaseFGCz_fg_ge_five hm (czBaseFG_fiveFG_of_sqfreeFour h m hm) N h5N

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_basePos_of_sqfreeFour

/-- **Endpoint (lane `bh-met-95`).**  The residual gives the target
`CharZeroK2BaseFGStatement`. -/
theorem czBaseFG_baseFG_of_sqfreeFour (h : czBaseFG_SqfreeFourStatement) :
    CharZeroK2BaseFGStatement :=
  charZeroK2BaseFG_of_pos (czBaseFG_basePos_of_sqfreeFour h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_baseFG_of_sqfreeFour

/-- The existing rank-four leaf `CZK2FngRankFourStatement` implies the residual. -/
theorem czBaseFG_sqfreeFour_of_rankFour (h : CZK2FngRankFourStatement) :
    czBaseFG_SqfreeFourStatement :=
  fun m hm _ ↦ h m (by omega)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_sqfreeFour_of_rankFour

/-- The existing rank-three leaf `czK2FngGtOne_RankThreeStatement` implies the residual. -/
theorem czBaseFG_sqfreeFour_of_rankThree (h : czK2FngGtOne_RankThreeStatement) :
    czBaseFG_SqfreeFourStatement :=
  czBaseFG_sqfreeFour_of_rankFour (czK2FngGtOne_rankFour_of_rankThree h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_sqfreeFour_of_rankThree

/-- Behr's statement for `SL_4(ℤ[1/m])` (`czRankFourFP_SLFourStatement`) implies the
residual. -/
theorem czBaseFG_sqfreeFour_of_slFour (h : czRankFourFP_SLFourStatement) :
    czBaseFG_SqfreeFourStatement :=
  czBaseFG_sqfreeFour_of_rankFour (czRankFourFP_k2FngRankFour_of_sl h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czBaseFG_sqfreeFour_of_slFour

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
