import GroupApproximation.Leavitt.RankTwelveCompressor
import GroupApproximation.Leavitt.HilbertHotelDefectNormal
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.FullRadicalClosureProperties
import GroupApproximation.Sofic.SimpleFullMFRadical

/-!
# The exact rank-twelve endpoint: definitions and closed algebra

This module fixes the group used in `non_mf_groups_exist.tex`:

`H = EL₁₂(L_{𝔽₂}(1,2))`.

The existing library already proves the following clauses at exactly this
rank:

* `H` is countable and has property `(T)`;
* the printed coefficient `q = s₁t₁` is nonzero;
* the printed defect `d = e₀₂(q)` is nontrivial; and
* `d` normally generates `H`.

The raw matrices `X`, `Y`, and `τ = diag(X,Y)`, their inverse identities,
Whitehead factorization, and the corner-conjugation calculation are in
`Leavitt.RankTwelveCompressor`.  This file names the required group-level lift
as `PrintedDefectConfiguration`; `RankTwelveConfiguration` constructs it by
flattening the nested block indices and proving elementary-group membership.

Likewise this file names the exact simplicity proposition without reproving
it.  `RankTwelveSimplicity.manuscriptPropositionSimple` closes it
unconditionally via exhaustive direct root extraction and elementary-root
normal generation, independently of the optional Preusser upper sandwich.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

/-- The coefficient ring `R = L_{𝔽₂}(1,2)` in the current manuscript. -/
abbrev R : Type := UniversalLeavitt.BinaryLeavittAlgebra

/-- Its canonical binary Leavitt family. -/
def leavittFamily : LeavittFamily R := UniversalLeavitt.family

/-- The exact group in `thm:headline`: `EL₁₂(L_{𝔽₂}(1,2))`. -/
noncomputable abbrev H : Type := BinaryLeavittSteinberg.ElementaryBase 12

/-- The complementary Leavitt idempotent `q = s₁t₁`. -/
def q : R := leavittFamily.p1

/-- The printed defect `d = e₀₂(q)` as an element of `H`. -/
noncomputable def defect : H :=
  elementaryRoot (0 : Fin 12) 2 (by decide) q

/-- The printed coefficient is nonzero. -/
theorem q_ne_zero : q ≠ 0 := by
  exact leavittFamily.p1_ne_zero

/-- The printed elementary defect is nontrivial. -/
theorem defect_ne_one : defect ≠ 1 := by
  change elGen (0 : Fin 12) 2 (by decide) leavittFamily.p1 ≠ 1
  exact LeavittMark.elGen_p1_ne_one leavittFamily 0 2 (by decide)

/-- **The normal-generation clause of `prop:defect`, closed at rank twelve.**
The proof is the Steinberg root-normal-generation theorem pushed through the
canonical surjection onto the elementary group. -/
theorem normalClosure_defect_eq_top :
    Subgroup.normalClosure ({defect} : Set H) = ⊤ := by
  simpa [defect, q] using
    (HilbertHotel.normalClosure_elementaryRoot_eq_top
      (n := 12) (by omega) (0 : Fin 12) 2 (by decide)
      (a := leavittFamily.p1) q_ne_zero)

/-- The exact rank-twelve group is nontrivial, witnessed by the printed
defect. -/
theorem nontrivial : Nontrivial H :=
  ⟨⟨defect, 1, defect_ne_one⟩⟩

/-- The exact rank-twelve group is finitely generated. -/
theorem finitelyGenerated : Group.FG H :=
  elementaryGroup_finitelyGenerated 12 (by omega)

/-- The exact rank-twelve group is countable. -/
theorem countable : Countable H :=
  countable_of_fg finitelyGenerated

local instance rankTwelveCountable : Countable H := countable

/-- The exact rank-twelve group has Kazhdan's property `(T)`. -/
theorem hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} H :=
  BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT (n := 12) (by omega)

/-- The closed simplicity-free structural profile used by the defect route. -/
theorem closedStructuralProfile :
    Countable H ∧ Group.FG H ∧ Nontrivial H ∧
      HasKazhdanPropertyT.{0, 0} H ∧
      defect ≠ 1 ∧ Subgroup.normalClosure ({defect} : Set H) = ⊤ :=
  ⟨countable, finitelyGenerated, nontrivial, hasKazhdanPropertyT,
    defect_ne_one, normalClosure_defect_eq_top⟩

/-! ## Exact interfaces for the two inputs closed by companion modules -/

/-- The manuscript's block ordering
`((a,b),i) ↦ 6a+3b+i` after matrix-composition has produced the associated
index as `(a,(b,i))`. -/
def frame12 : Fin 2 × (Fin 2 × Fin 3) ≃ Fin 12 where
  toFun x := ⟨x.2.2.val + 3 * x.2.1.val + 6 * x.1.val, by
    have h1 := x.1.isLt
    have h2 := x.2.1.isLt
    have h3 := x.2.2.isLt
    omega⟩
  invFun n := (⟨n.val / 6, by have := n.isLt; omega⟩,
    (⟨n.val / 3 % 2, by omega⟩, ⟨n.val % 3, by omega⟩))
  left_inv := by decide
  right_inv := by decide

/-- Flatten the nested block ring used by `RankTwelveCompressor` to the
literal `12 × 12` matrix ring. -/
def flat12 : RankTwelve.Full R ≃+* Matrix (Fin 12) (Fin 12) R :=
  (((Matrix.compRingEquiv (Fin 2) (Fin 3) R).mapMatrix (m := Fin 2)).trans
    (Matrix.compRingEquiv (Fin 2) (Fin 2 × Fin 3) R)).trans
      (Matrix.reindexRingEquiv R frame12)

/-- The literal flattened unit `tau = diag(X,Y)` from `eq:tau`, before
proving that it belongs to the elementary subgroup. -/
noncomputable def printedTauGL : (Matrix (Fin 12) (Fin 12) R)ˣ :=
  Units.mapEquiv flat12.toMulEquiv (RankTwelve.tauUnit leavittFamily)

/-- The inclusion of the upper-left three indices. -/
def cornerIndex (i : Fin 3) : Fin 12 :=
  ⟨i.val, by have := i.isLt; omega⟩

theorem cornerIndex_injective : Function.Injective cornerIndex := by
  intro i j hij
  apply Fin.val_injective
  have hval := congrArg (fun x : Fin 12 ↦ x.val) hij
  exact hval

/-- The elementary roots supported on the upper-left `3 × 3` corner. -/
def cornerRootSet : Set H :=
  {x | ∃ (i j : Fin 3) (hij : i ≠ j) (a : R),
    elementaryRoot (cornerIndex i) (cornerIndex j)
      (cornerIndex_injective.ne hij) a = x}

/-- The literal upper-left `EL₃(R)` subgroup of `H`. -/
noncomputable def corner : Subgroup H := Subgroup.closure cornerRootSet

/-- The printed centralizer mark `c = e₃₄(1)`. -/
noncomputable def c : H :=
  elementaryRoot (3 : Fin 12) 4 (by decide) 1

/-- The printed corner element `ell = e₁₂(1)`. -/
noncomputable def ell : H :=
  elementaryRoot (1 : Fin 12) 2 (by decide) 1

/-- The printed element `ell` belongs to the upper-left corner. -/
theorem ell_mem_corner : ell ∈ corner := by
  apply Subgroup.subset_closure
  refine ⟨(1 : Fin 3), (2 : Fin 3), by decide, 1, ?_⟩
  apply Subtype.ext
  simp [ell, cornerIndex]

/-- The printed mark `c=e₃₄(1)` centralizes the entire upper-left
corner.  This is purely a disjoint-support elementary-matrix calculation. -/
theorem c_commutes_corner : ∀ gamma ∈ corner, Commute c gamma := by
  intro gamma hgamma
  rw [corner] at hgamma
  induction hgamma using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      unfold c
      exact elementaryRoot_commute_of_ne
        (3 : Fin 12) 4 (cornerIndex i) (cornerIndex j)
        (by decide) (cornerIndex_injective.ne hij)
        (by
          intro h
          have hv := congrArg Fin.val h
          simp [cornerIndex] at hv
          omega)
        (by
          intro h
          have hv := congrArg Fin.val h
          simp [cornerIndex] at hv
          omega)
        1 a
  | one => exact Commute.one_right c
  | mul x y _ _ hx hy => exact hx.mul_right hy
  | inv x _ hx => exact hx.inv_right

/-- The exact remaining group-level content of `prop:defect`.

The subgroup is the upper-left `EL₃` corner; `tau`, `c`, and `ell` must be the
flattened elements represented by the matrices printed in the manuscript.  The
raw identities needed to construct these witnesses are already theorems in
`RankTwelveCompressor`; the missing work is their lift through flattening and
elementary-group membership.

The condition is deliberately stated using a one-sided compressor itself,
matching the current manuscript rather than the stronger subgroup generated by
all compressors used in older files. -/
def PrintedDefectConfiguration : Prop :=
  ∃ htau : printedTauGL ∈ elementaryGroup (Fin 12) R,
    let tau : H := ⟨printedTauGL, htau⟩
    HasKazhdanPropertyT.{0, 0} corner ∧
      (∀ gamma ∈ corner, tau * gamma * tau⁻¹ ∈ corner) ∧
      ⁅tau * c * tau⁻¹, ell⁆ = defect

/-- The exact content of `prop:simple`, kept as a named proposition so audits
can distinguish the final simplicity theorem from its root-normal-generation
support.  It is proved by `RankTwelveSimplicity.manuscriptPropositionSimple`. -/
def PropositionSimple : Prop := IsSimpleGroup H

/-- The group-level printed configuration makes the printed defect equal to
the whole rank-twelve group.  This uses the already closed normal-generation
theorem for `d`; it does not use simplicity. -/
theorem printedDefect_eq_top_of_configuration
    (hconfiguration : PrintedDefectConfiguration) :
    printedDefect corner = ⊤ := by
  obtain ⟨_, _, hcompresses, hcomm⟩ := hconfiguration
  have hd : defect ∈ printedDefect corner := by
    rw [← hcomm]
    exact printedDefect_generator_mem corner hcompresses c_commutes_corner
      ell_mem_corner
  have hclosure : Subgroup.normalClosure ({defect} : Set H) ≤
      printedDefect corner := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hd
  apply top_unique
  rw [← normalClosure_defect_eq_top]
  exact hclosure

/-- The group-level printed configuration alone closes the full-radical
calculation in `thm:headline`.  The proof is exactly the current manuscript's
route: the displayed defect normally generates, so the printed defect
saturates, and the one-sided compression criterion applies. -/
theorem residual_eq_top_of_configuration
    (hconfiguration : PrintedDefectConfiguration) :
    actualCoronaMFResidual H = ⊤ := by
  letI : Countable H := countable
  have htop : printedDefect corner = ⊤ :=
    printedDefect_eq_top_of_configuration hconfiguration
  obtain ⟨_, hcornerT, _, _⟩ := hconfiguration
  have hfull :=
    (manuscriptOneSidedCompressionCriterion (G := H) corner hcornerT).2.2
      hasKazhdanPropertyT htop
  rwa [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual] at hfull

/-- The exact conclusion of `thm:headline`, including both readings of the
full MF radical asserted in the manuscript. -/
def HeadlineConclusion : Prop :=
  Nontrivial H ∧
    IsSimpleGroup H ∧
    HasKazhdanPropertyT.{0, 0} H ∧
    actualCoronaMFResidual H = ⊤ ∧
    (∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1) ∧
    ¬ IsCDEOperatorMF H

/-! ## Assembling the headline from the two named inputs -/

/-- A nontrivial countable group with full actual corona MF residual is not
MF in the literal CDE sense. -/
theorem not_isCDEOperatorMF_of_residual_eq_top
    (hfull : actualCoronaMFResidual H = ⊤) :
    ¬ IsCDEOperatorMF H := by
  letI : Countable H := countable
  letI : Nontrivial H := nontrivial
  exact not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hfull

/-- Once simplicity and the full-radical calculation are available, every
remaining clause of `thm:headline` is already closed.  This theorem makes the
dependency boundary exact: it consumes no matrix or normal-subgroup fact other
than those two named propositions. -/
theorem headlineConclusion_of
    (hsimple : PropositionSimple)
    (hfull : actualCoronaMFResidual H = ⊤) :
    HeadlineConclusion := by
  letI : Countable H := countable
  letI : Nontrivial H := nontrivial
  have hnot : ¬ IsCDEOperatorMF H :=
    not_isCDEOperatorMF_of_residual_eq_top hfull
  refine ⟨nontrivial, hsimple, hasKazhdanPropertyT, hfull, ?_, hnot⟩
  intro M _ _ hM f x
  exact eq_one_of_isSimpleGroup_of_target_isCDEOperatorMF
    hsimple hnot hM f x

/-- Consequently the current headline has exactly two unresolved inputs:
the rank-twelve group-level realization of the printed matrices and the
normal-subgroup/simplicity theorem. -/
theorem headlineConclusion_of_configuration_and_simplicity
    (hconfiguration : PrintedDefectConfiguration)
    (hsimple : PropositionSimple) :
    HeadlineConclusion :=
  headlineConclusion_of hsimple
    (residual_eq_top_of_configuration hconfiguration)

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
