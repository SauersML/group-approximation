import GroupApproximation.Monsters.LiteralCyclicCalibration
import GroupApproximation.Sofic.CliffordBSAmenableMF
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Sofic.LEFMarkedCompression
import GroupApproximation.Sofic.MFCamouflageRadical
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.UniversalFactorization
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Quotient phase transitions and two-tier invisibility

This file records the two main consequences of camouflage surgery.

* If every quotient of the visible group is MF, semantic closure is obtained
  by adjoining the one hidden kernel.  Hence killing the distinguished defect
  exactly classifies MF quotients.
* If a visible MF group has an element killed by every exact linear model but
  detected by a matrix corona, camouflage preserves that separation while
  adding a lower, fully MF-invisible tier.

The final section connects the second abstract theorem to Cairn's literal
cyclic calibration.  Its exact finite-dimensional kill and its explicit
corona detector are unconditional; MF-ness of that calibration remains an
explicit premise, matching the current Shulman-permanence boundary in the
repository.
-/

namespace GroupApproximation
namespace MFCamouflage

noncomputable section

variable {B Q : Type} [Group B] [Group Q]

/-- The preimage of the image of a subgroup is obtained by adjoining the
kernel.  This elementary identity makes the cyclic phase formula literal. -/
theorem comap_map_eq_sup_ker (f : B →* Q) (N : Subgroup B) :
    (N.map f).comap f = N ⊔ f.ker := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hk : x * y⁻¹ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hyx]
      exact mul_inv_cancel _
    have hxprod : x = (x * y⁻¹) * y := by group
    rw [hxprod]
    exact (N ⊔ f.ker).mul_mem
      ((le_sup_right : f.ker ≤ N ⊔ f.ker) hk)
      ((le_sup_left : N ≤ N ⊔ f.ker) hy)
  · refine sup_le ?_ ?_
    · intro x hx
      exact ⟨x, hx, rfl⟩
    · intro x hx
      apply Subgroup.mem_comap.mpr
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _

local instance consequenceQuotientCountable
    (Q : Type) [Group Q] [Countable Q] (M : Subgroup Q) [M.Normal] :
    Countable (Q ⧸ M) :=
  Function.Surjective.countable (QuotientGroup.mk'_surjective M)

local instance multiplicativeIntCountable : Countable (Multiplicative ℤ) :=
  Countable.of_equiv ℤ Multiplicative.toAdd

/-- Every countable cyclic group is operator-MF: Mathlib identifies it with
`Multiplicative (ZMod n)`; `n = 0` is the integers and `n ≠ 0` is finite. -/
theorem isCDEOperatorMF_of_isCyclic (G : Type) [Group G] [Countable G]
    [IsCyclic G] : IsCDEOperatorMF G := by
  apply (isCDEOperatorMF_iff_isOperatorMF G).mpr
  let e : Multiplicative (ZMod (Nat.card G)) ≃* G :=
    zmodCyclicMulEquiv (inferInstance : IsCyclic G)
  apply CommensurabilityInvariance.isOperatorMF_of_mulEquiv e
  by_cases hcard : Nat.card G = 0
  · rw [hcard]
    exact LiteralLEFExtension.integerQuotient_isOperatorMF
  · letI : NeZero (Nat.card G) := ⟨hcard⟩
    exact isOperatorMF_of_finite_standard (Multiplicative (ZMod (Nat.card G)))

/-- Every quotient of the infinite cyclic group is MF. -/
theorem multiplicativeInt_quotient_isCDEOperatorMF
    (M : Subgroup (Multiplicative ℤ)) [M.Normal] :
    IsCDEOperatorMF (Multiplicative ℤ ⧸ M) := by
  letI : IsCyclic (Multiplicative ℤ ⧸ M) :=
    isCyclic_of_surjective (QuotientGroup.mk' M)
      (QuotientGroup.mk'_surjective M)
  exact isCDEOperatorMF_of_isCyclic _

/-- If every quotient of `Q` is MF, the closure of any relation set is exactly
that relation set joined with the hidden kernel. -/
theorem closure_eq_sup_ker_of_all_quotients_mf
    (d : B) (Q : Type) [Group Q] [Countable B] [Countable Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (hall : ∀ (M : Subgroup Q) [M.Normal], IsCDEOperatorMF (Q ⧸ M))
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    actualCoronaMFClosure N = N ⊔ (projection d Q).ker := by
  rw [actualCoronaMFClosure_eq_comap d Q hfull N,
    (actualCoronaMFClosure_eq_self_iff
      (N.map (projection d Q))).mpr (hall _),
    comap_map_eq_sup_ker]

/-- **One-word quotient classification.**  When the visible group has only MF
quotients and `d` normally generates the hidden vertex, a quotient of the
camouflage group is MF exactly when its relation subgroup contains the single
distinguished defect. -/
theorem quotient_isCDEOperatorMF_iff_defect_mem
    (d : B) (Q : Type) [Group Q] [Countable B] [Countable Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (hgen : Subgroup.normalClosure ({d} : Set B) = ⊤)
    (hall : ∀ (M : Subgroup Q) [M.Normal], IsCDEOperatorMF (Q ⧸ M))
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    IsCDEOperatorMF (Camouflage d Q ⧸ N) ↔ defect d Q ∈ N := by
  rw [quotient_isCDEOperatorMF_iff d Q hfull N]
  constructor
  · rintro ⟨hker, _⟩
    apply hker
    rw [projection_ker_eq_normalClosure d Q hgen]
    exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  · intro hd
    constructor
    · rw [projection_ker_eq_normalClosure d Q hgen]
      exact Subgroup.normalClosure_le_normal
        (Set.singleton_subset_iff.mpr hd)
    · exact hall _

/-- Hilbert-hotel specialization of the full closure formula. -/
theorem Hotel.closure_eq_sup_ker_of_all_quotients_mf
    (Q : Type) [Group Q] [Countable Q]
    (hall : ∀ (M : Subgroup Q) [M.Normal], IsCDEOperatorMF (Q ⧸ M))
    (N : Subgroup (Hotel.Camouflage Q)) [N.Normal] :
    actualCoronaMFClosure N =
      N ⊔ (projection Hotel.sourceDefect Q).ker :=
  GroupApproximation.MFCamouflage.closure_eq_sup_ker_of_all_quotients_mf
    Hotel.sourceDefect Q
    Hotel.source_actualCoronaMFResidual_eq_top hall N

/-- Hilbert-hotel specialization of the one-word phase transition. -/
theorem Hotel.quotient_isCDEOperatorMF_iff_defect_mem
    (Q : Type) [Group Q] [Countable Q]
    (hall : ∀ (M : Subgroup Q) [M.Normal], IsCDEOperatorMF (Q ⧸ M))
    (N : Subgroup (Hotel.Camouflage Q)) [N.Normal] :
    IsCDEOperatorMF (Hotel.Camouflage Q ⧸ N) ↔
      defect Hotel.sourceDefect Q ∈ N :=
  GroupApproximation.MFCamouflage.quotient_isCDEOperatorMF_iff_defect_mem
    Hotel.sourceDefect Q
    Hotel.source_actualCoronaMFResidual_eq_top
    Hotel.sourceDefect_normallyGenerates hall N

/-- The concrete cyclic camouflage group. -/
noncomputable abbrev Hotel.Cyclic : Type :=
  Hotel.Camouflage (Multiplicative ℤ)

/-- For every normal relation subgroup of the concrete cyclic camouflage,
MF semantic closure is obtained by adjoining the one hidden kernel. -/
theorem Hotel.cyclic_closure_eq_sup_ker
    (N : Subgroup Hotel.Cyclic) [N.Normal] :
    actualCoronaMFClosure N =
      N ⊔ (projection Hotel.sourceDefect (Multiplicative ℤ)).ker :=
  Hotel.closure_eq_sup_ker_of_all_quotients_mf (Multiplicative ℤ)
    multiplicativeInt_quotient_isCDEOperatorMF N

/-- The same formula with the hidden kernel expanded as the normal closure of
the one fixed defect word. -/
theorem Hotel.cyclic_closure_eq_sup_normalClosure
    (N : Subgroup Hotel.Cyclic) [N.Normal] :
    actualCoronaMFClosure N =
      N ⊔ Subgroup.normalClosure
        ({defect Hotel.sourceDefect (Multiplicative ℤ)} : Set Hotel.Cyclic) := by
  rw [Hotel.cyclic_closure_eq_sup_ker,
    Hotel.projection_ker_eq_normalClosure]

/-- A single fixed word classifies every MF quotient of the concrete cyclic
camouflage group. -/
theorem Hotel.cyclic_quotient_isCDEOperatorMF_iff_defect_mem
    (N : Subgroup Hotel.Cyclic) [N.Normal] :
    IsCDEOperatorMF (Hotel.Cyclic ⧸ N) ↔
      defect Hotel.sourceDefect (Multiplicative ℤ) ∈ N :=
  Hotel.quotient_isCDEOperatorMF_iff_defect_mem (Multiplicative ℤ)
    multiplicativeInt_quotient_isCDEOperatorMF N

/-- **Fixed-relation classification of all MF quotients of `W_ℤ`.**
The quotient by `N` is operator-MF exactly when `N` contains the single
distinguished defect, independently of every other relation in `N`. -/
theorem Hotel.cyclic_quotient_isOperatorMF_iff_defect_mem
    (N : Subgroup Hotel.Cyclic) [N.Normal] :
    IsOperatorMF (Hotel.Cyclic ⧸ N) ↔
      defect Hotel.sourceDefect (Multiplicative ℤ) ∈ N := by
  rw [← isCDEOperatorMF_iff_isOperatorMF]
  exact Hotel.cyclic_quotient_isCDEOperatorMF_iff_defect_mem N

/-! ## Exact versus asymptotic visibility -/

/-- If every all-fields finite-dimensional representation of `B` is trivial,
then the camouflage kernel lies in the all-fields linear residual. -/
theorem projection_ker_le_linearResidual
    (d : B) (Q : Type) [Group Q]
    (hlinear : ∀ (F : Type) (_ : Field F) (n : ℕ)
      (f : B →* Matrix (Fin n) (Fin n) F), f = 1) :
    (projection d Q).ker ≤ linearResidual (Camouflage d Q) := by
  intro x hx F hF n rho
  letI : Field F := hF
  have hkill : rho.comp (blackHole d Q) = 1 :=
    hlinear F hF n _
  have hfactor := factor_through_projection d Q rho hkill
  have heval := DFunLike.congr_fun hfactor x
  have hx1 := MonoidHom.mem_ker.mp hx
  change rho (visible d Q (projection d Q x)) = rho x at heval
  rw [hx1, map_one, map_one] at heval
  exact heval.symm

/-- The all-fields linear residual is transplanted whenever the hidden vertex
is linearly invisible. -/
theorem linearResidual_eq_comap
    (d : B) (Q : Type) [Group Q]
    (hlinear : ∀ (F : Type) (_ : Field F) (n : ℕ)
      (f : B →* Matrix (Fin n) (Fin n) F), f = 1) :
    linearResidual (Camouflage d Q) =
      (linearResidual Q).comap (projection d Q) :=
  UniversalFactorization.linearResidual_eq_comap (projection d Q)
    (projection_surjective d Q)
    (projection_ker_le_linearResidual d Q hlinear)

/-- **Two-tier matricial invisibility.**  A linearly invisible but
corona-visible word in an MF visible group produces a strict gap in the
camouflage group. -/
theorem actualCoronaMFResidual_lt_linearResidual
    (d : B) (Q : Type) [Group Q] [Countable Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (hlinear : ∀ (F : Type) (_ : Field F) (n : ℕ)
      (f : B →* Matrix (Fin n) (Fin n) F), f = 1)
    (hQ : IsCDEOperatorMF Q) (w : Q)
    (hwLinear : w ∈ linearResidual Q)
    (hwVisible : w ∉ actualCoronaMFResidual Q) :
    actualCoronaMFResidual (Camouflage d Q) < linearResidual (Camouflage d Q) := by
  have hrad : actualCoronaMFResidual (Camouflage d Q) = (projection d Q).ker :=
    actualCoronaMFResidual_eq_ker d Q hfull hQ
  have hle : actualCoronaMFResidual (Camouflage d Q) ≤
      linearResidual (Camouflage d Q) := by
    rw [hrad]
    exact projection_ker_le_linearResidual d Q hlinear
  have hwordLinear : visible d Q w ∈ linearResidual (Camouflage d Q) := by
    rw [linearResidual_eq_comap d Q hlinear]
    exact hwLinear
  have hwordVisible : visible d Q w ∉
      actualCoronaMFResidual (Camouflage d Q) := by
    rw [actualCoronaMFResidual_eq_comap d Q hfull]
    exact hwVisible
  apply lt_of_le_of_ne hle
  intro heq
  apply hwordVisible
  rw [heq]
  exact hwordLinear

/-! ## The literal BS calibration supplies the separating word -/

open LiteralCyclicCalibration

/-- Cairn's literal cyclic mark is killed by every matrix representation over
every field, hence belongs to the all-fields linear residual. -/
theorem literalCyclic_mark_mem_linearResidual :
    mark ∈ linearResidual LiteralGroup := by
  intro F hF n rho
  classical
  letI : Field F := hF
  let e := Matrix.toLinAlgEquiv' (n := Fin n) (R := F)
  let hEnd : LiteralGroup →* Module.End F (Fin n → F) :=
    e.toRingEquiv.toMulEquiv.toMonoidHom.comp rho
  have hkill := finiteDimensional_kill (MonoidHom.toHomUnits hEnd)
  have hend : hEnd mark = 1 := by
    have hcoe := congrArg
      (fun z : (Module.End F (Fin n → F))ˣ ↦
        (z : Module.End F (Fin n → F))) hkill
    simpa using hcoe
  have hmatrix := congrArg (fun z ↦ e.symm z) hend
  simpa [hEnd] using hmatrix

/-- The same literal mark is detected by the explicit operator-norm corona
model. -/
theorem literalCyclic_mark_not_mem_actualCoronaMFResidual :
    mark ∉ actualCoronaMFResidual LiteralGroup :=
  CliffordBSAmenableMF.mark_not_actualCoronaMFInvisible

/-- Conditional only at the precise current permanence boundary: once the
literal calibration group is supplied as MF, the general compiler yields the
strict two-tier gap. -/
theorem hotelLiteral_actualCoronaMFResidual_lt_linearResidual
    (hlinearHotel : ∀ (F : Type) (_ : Field F) (n : ℕ)
      (f : Hotel.BlackHole →* Matrix (Fin n) (Fin n) F), f = 1)
    (hLiteralMF : IsCDEOperatorMF LiteralGroup) :
    actualCoronaMFResidual (Hotel.Camouflage LiteralGroup) <
      linearResidual (Hotel.Camouflage LiteralGroup) :=
  actualCoronaMFResidual_lt_linearResidual Hotel.sourceDefect LiteralGroup
    Hotel.source_actualCoronaMFResidual_eq_top hlinearHotel hLiteralMF mark
    literalCyclic_mark_mem_linearResidual
    literalCyclic_mark_not_mem_actualCoronaMFResidual

end
end MFCamouflage
end GroupApproximation
