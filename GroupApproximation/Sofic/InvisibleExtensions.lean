import GroupApproximation.Manuscript.OneSidedMFRadical.PrescribedQuotients
import GroupApproximation.Sofic.MFCamouflageConsequences
import GroupApproximation.Sofic.MFBlackHoleAttachment
import GroupApproximation.Sofic.MatricialStabilityInstances
import GroupApproximation.Sofic.SplitMFStability

/-!
# Invisible extensions in matricial approximation

This is the paper-facing construction endpoint.  A fixed finitely presented
full-MF-radical group with one normal generator is attached to an arbitrary
visible group `Q`.  The result has a split projection to `Q`; every MF or
norm-matrix-corona observer factors uniquely through that projection; and,
when `Q` is MF, its exact MF radical is the normal closure of one fixed defect.

The second half exposes the semantic relation calculus and the fixed source
`U_X = C(F_X)`.  It is the formal compiler interface presently justified by
the library: arbitrary normal relations in `U_X` are evaluated entirely in
their visible image in `F_X`.  No claim is made here that a canonical finite
relator list has been extracted from the abstract finite-presentation proof.
-/

namespace GroupApproximation
namespace InvisibleExtensions

open MatricialStabilityRadical MatricialStabilityInstances

local instance multiplicativeIntCountable : Countable (Multiplicative ℤ) :=
  Countable.of_equiv ℤ Multiplicative.toAdd

local instance quotientCountable
    {G : Type} [Group G] [Countable G] (N : Subgroup G) [N.Normal] :
    Countable (G ⧸ N) :=
  Function.Surjective.countable (QuotientGroup.mk'_surjective N)

/-! ## The fixed black hole -/

/-- The fixed black-hole group used by every extension. -/
abbrev BlackHole : Type := MFCamouflage.Hotel.BlackHole

/-- Its single distinguished normal generator. -/
noncomputable abbrev blackHoleDefect : BlackHole :=
  MFCamouflage.Hotel.sourceDefect

/-- **Fixed black-hole package.**  The seed is finitely presented, its MF
radical is the whole group, and one nontrivial element normally generates it.
Thus every homomorphism from it into a countable MF group, or into a standard
norm-matrix corona, is trivial. -/
theorem fixed_black_hole :
    Group.IsFinitelyPresented BlackHole ∧
      blackHoleDefect ≠ 1 ∧
      normMFResidual BlackHole = ⊤ ∧
      Subgroup.normalClosure ({blackHoleDefect} : Set BlackHole) = ⊤ := by
  refine ⟨inferInstance, MFCamouflage.Hotel.sourceDefect_ne_one, ?_,
    MFCamouflage.Hotel.sourceDefect_normallyGenerates⟩
  calc
    normMFResidual BlackHole = coronaMFResidual BlackHole :=
      (coronaMFResidual_eq_normMFResidual (G := BlackHole)).symm
    _ = actualCoronaMFResidual BlackHole :=
      (actualCoronaMFResidual_eq_coronaMFResidual (G := BlackHole)).symm
    _ = ⊤ := MFCamouflage.Hotel.source_actualCoronaMFResidual_eq_top

/-! ## The invisible-extension machine -/

/-- The invisible extension `C(Q)` of a visible group `Q`. -/
noncomputable abbrev Extension (Q : Type) [Group Q] : Type :=
  MFCamouflage.Hotel.Camouflage Q

/-- The fixed hidden switch in `C(Q)`. -/
noncomputable abbrev defect (Q : Type) [Group Q] : Extension Q :=
  MFCamouflage.defect blackHoleDefect Q

/-- The split projection from `C(Q)` to its visible quotient. -/
noncomputable abbrev projection (Q : Type) [Group Q] : Extension Q →* Q :=
  MFCamouflage.projection blackHoleDefect Q

/-- The canonical section of the visible quotient. -/
noncomputable abbrev visibleSection (Q : Type) [Group Q] : Q →* Extension Q :=
  MFCamouflage.visible blackHoleDefect Q

/-- **Invisible-extension theorem.**  For every countable visible group `Q`,
`C(Q) → Q` is split, the hidden switch survives algebraically, the MF
radical is transplanted from `Q`, and every countable MF observer sees exactly
the maps out of `Q`. -/
theorem invisible_extension
    (Q : Type) [Group Q] [Countable Q] :
    Function.Surjective (projection Q) ∧
      (projection Q).comp (visibleSection Q) = MonoidHom.id Q ∧
      defect Q ≠ 1 ∧
      normMFResidual (Extension Q) =
        (normMFResidual Q).comap (projection Q) ∧
      (∀ (M : Type) [Group M] [Countable M], IsOperatorMF M →
        Function.Bijective
          (fun f : Q →* M ↦ f.comp (projection Q))) := by
  refine ⟨MFCamouflage.projection_surjective blackHoleDefect Q,
    MFCamouflage.projection_comp_visible blackHoleDefect Q,
    MFCamouflage.Hotel.camouflage_defect_ne_one Q, ?_, ?_⟩
  · simpa only [actualCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual] using
      MFCamouflage.Hotel.actualCoronaMFResidual_eq_comap Q
  · intro M _ _ hM
    exact MFCamouflage.Hotel.operatorMF_precomp_bijective Q hM

/-- Literal finite-dimensional-approximation form: precomposition is a
bijection for every positive sequence of genuine norm-matrix coronas. -/
theorem corona_observers_see_only_the_quotient
    (Q : Type) [Group Q]
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (fun f : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        f.comp (projection Q)) := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  exact MFCamouflage.actualCorona_precomp_bijective blackHoleDefect Q
    MFCamouflage.Hotel.source_actualCoronaMFResidual_eq_top X hX

/-- If the visible group is MF, the extension has exactly one normally
generated invisible kernel and its MF-visible quotient is literally `Q`. -/
theorem exact_radical_of_visible_mf
    (Q : Type) [Group Q] [Countable Q] (hQ : IsOperatorMF Q) :
    normMFResidual (Extension Q) = (projection Q).ker ∧
      (projection Q).ker =
        Subgroup.normalClosure ({defect Q} : Set (Extension Q)) ∧
      ¬ IsOperatorMF (Extension Q) := by
  have hQCDE : IsCDEOperatorMF Q :=
    (isCDEOperatorMF_iff_isOperatorMF Q).mpr hQ
  refine ⟨?_, MFCamouflage.Hotel.projection_ker_eq_normalClosure Q,
    MFCamouflage.Hotel.not_isOperatorMF Q hQ⟩
  calc
    normMFResidual (Extension Q) =
        actualCoronaMFResidual (Extension Q) := by
      rw [actualCoronaMFResidual_eq_coronaMFResidual,
        coronaMFResidual_eq_normMFResidual]
    _ = (projection Q).ker :=
      MFCamouflage.actualCoronaMFResidual_eq_ker blackHoleDefect Q
        MFCamouflage.Hotel.source_actualCoronaMFResidual_eq_top hQCDE

/-- Finite presentation is preserved by invisible extension. -/
theorem extension_isFinitelyPresented
    (Q : Type) [Group Q] [Group.IsFinitelyPresented Q] :
    Group.IsFinitelyPresented (Extension Q) :=
  MFCamouflage.Hotel.isFinitelyPresented Q

/-- Killing the one fixed hidden switch literally recovers the prescribed
visible group, independently of whether that group is MF. -/
theorem defect_quotient_equiv
    (Q : Type) [Group Q] :
    Nonempty
      (Extension Q ⧸ Subgroup.normalClosure ({defect Q} : Set (Extension Q))
        ≃* Q) := by
  have hker : (projection Q).ker =
      Subgroup.normalClosure ({defect Q} : Set (Extension Q)) :=
    MFCamouflage.Hotel.projection_ker_eq_normalClosure Q
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (projection Q) (MFCamouflage.projection_surjective blackHoleDefect Q))⟩

/-- For an MF visible group, its prescribed copy is exactly the quotient of
the extension by the extension's MF radical. -/
theorem mf_visible_quotient_equiv
    (Q : Type) [Group Q] [Countable Q] (hQ : IsOperatorMF Q) :
    Nonempty (Extension Q ⧸ normMFResidual (Extension Q) ≃* Q) := by
  have hrad : normMFResidual (Extension Q) = (projection Q).ker :=
    (exact_radical_of_visible_mf Q hQ).1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hrad).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (projection Q) (MFCamouflage.projection_surjective blackHoleDefect Q))⟩

/-! ## Semantic relation gadgets -/

/-- **General black-hole attachment.**  If `B` has full MF radical, attaching
it to `G` along `C` is indistinguishable, to every countable MF target, from
algebraically quotienting `G` by the normal closure of the attached edge
image. -/
theorem black_hole_attachment_gadget
    {B C G : Type} [Group B] [Group C] [Group G]
    (left : C →* B) (right : C →* G)
    (hfull : actualCoronaMFResidual B = ⊤) :
    Function.Surjective (MFBlackHoleAttachment.projection left right) ∧
      actualCoronaMFResidual (MFBlackHoleAttachment.Attachment left right) =
        (actualCoronaMFResidual
          (MFBlackHoleAttachment.VisibleQuotient right)).comap
            (MFBlackHoleAttachment.projection left right) ∧
      (∀ (M : Type) [Group M] [Countable M], IsOperatorMF M →
        Function.Bijective
          (fun f : MFBlackHoleAttachment.VisibleQuotient right →* M ↦
            f.comp (MFBlackHoleAttachment.projection left right))) := by
  exact ⟨MFBlackHoleAttachment.projection_surjective left right,
    MFBlackHoleAttachment.actualCoronaMFResidual_eq_comap left right hfull,
    fun _ _ _ hM ↦
      MFBlackHoleAttachment.operatorMF_precomp_bijective
        left right hfull hM⟩

/-- A finite black-hole attachment preserves finite presentability whenever
the black-hole and visible vertices are finitely presented and the edge group
is finitely generated. -/
theorem black_hole_attachment_isFinitelyPresented
    {B C G : Type} [Group B] [Group C] [Group G]
    (left : C →* B) (right : C →* G)
    [Group.IsFinitelyPresented B] [Group.IsFinitelyPresented G] [Group.FG C] :
    Group.IsFinitelyPresented
      (MFBlackHoleAttachment.Attachment left right) :=
  MFBlackHoleAttachment.isFinitelyPresented left right

/-- **One-word MF-invisible relation cell.**  When one attached edge element
normally generates the black hole and the visible semantic quotient has
trivial MF radical, that element survives algebraically but normally
generates the exact MF radical of the attachment. -/
theorem one_word_relation_cell
    {B C G : Type} [Group B] [Group C] [Group G]
    (left : C →* B) (right : C →* G)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hfull : actualCoronaMFResidual B = ⊤)
    (hvisible : actualCoronaMFResidual
      (MFBlackHoleAttachment.VisibleQuotient right) = ⊥)
    (c : C) (hc : left c ≠ 1)
    (hgen : Subgroup.normalClosure ({left c} : Set B) = ⊤) :
    let d := MFBlackHoleAttachment.blackHole left right (left c)
    d ≠ 1 ∧
      actualCoronaMFResidual (MFBlackHoleAttachment.Attachment left right) =
        Subgroup.normalClosure
          ({d} : Set (MFBlackHoleAttachment.Attachment left right)) := by
  dsimp
  exact ⟨MFBlackHoleAttachment.edge_survives
      left right hleft hright c hc,
    MFBlackHoleAttachment.actualCoronaMFResidual_eq_normalClosure_one
      left right hfull hvisible c hgen⟩

/-- **Semantic attachment theorem for the invisible extension.**  Adding an
arbitrary normal relation subgroup `N` to `C(Q)` has MF meaning determined
exactly by the image of `N` in `Q`.  In particular, the quotient is MF exactly
when the relations kill the fixed hidden kernel and their visible quotient is
MF. -/
theorem semantic_relation_calculus
    (Q : Type) [Group Q] [Countable Q]
    (N : Subgroup (Extension Q)) [N.Normal] :
    actualCoronaMFClosure N =
        (actualCoronaMFClosure (N.map (projection Q))).comap (projection Q) ∧
      (IsCDEOperatorMF (Extension Q ⧸ N) ↔
        (projection Q).ker ≤ N ∧
          IsCDEOperatorMF (Q ⧸ N.map (projection Q))) := by
  exact ⟨MFCamouflage.Hotel.actualCoronaMFClosure_eq_comap Q N,
    MFCamouflage.quotient_isCDEOperatorMF_iff blackHoleDefect Q
      MFCamouflage.Hotel.source_actualCoronaMFResidual_eq_top N⟩

/-! ## One fixed source per generator type -/

/-- The universal camouflage source on a generator type `X`. -/
noncomputable abbrev UniversalSource (X : Type) : Type :=
  Extension (FreeGroup X)

/-- Its visible free-group projection. -/
noncomputable abbrev universalProjection (X : Type) :
    UniversalSource X →* FreeGroup X :=
  projection (FreeGroup X)

/-- The same fixed hidden switch in every quotient compiled from `U_X`. -/
noncomputable abbrev universalDefect (X : Type) : UniversalSource X :=
  defect (FreeGroup X)

/-- **Universal semantic compiler.**  One fixed `U_X = C(F_X)` handles every
normal relation subgroup `N`: its complete MF closure and MF quotient test are
computed in the visible free group.  This is the theorem-level gadget
interface; a syntactic relator-list compiler is intentionally a separate
effectivity problem. -/
theorem universal_source_relation_calculus
    (X : Type) [Countable X]
    (N : Subgroup (UniversalSource X)) [N.Normal] :
    actualCoronaMFClosure N =
        (actualCoronaMFClosure
          (N.map (universalProjection X))).comap (universalProjection X) ∧
      (IsCDEOperatorMF (UniversalSource X ⧸ N) ↔
        (universalProjection X).ker ≤ N ∧
          IsCDEOperatorMF
            (FreeGroup X ⧸ N.map (universalProjection X))) := by
  letI : Countable (FreeGroup X) := freeGroupCountable
  exact semantic_relation_calculus (FreeGroup X) N

/-- For a finite generator type, the universal source is one fixed finitely
presented group. -/
theorem universal_source_isFinitelyPresented
    (X : Type) [Finite X] :
    Group.IsFinitelyPresented (UniversalSource X) :=
  extension_isFinitelyPresented (FreeGroup X)

/-- **Fixed-source profile.**  For every finite generator type, `U_X` is one
fixed finitely presented non-MF group whose MF radical is generated by the
single universal switch.  The visible free group is MF. -/
theorem universal_source_profile
    (X : Type) [Finite X] :
    Group.IsFinitelyPresented (UniversalSource X) ∧
      IsOperatorMF (FreeGroup X) ∧
      ¬ IsOperatorMF (UniversalSource X) ∧
      universalDefect X ≠ 1 ∧
      normMFResidual (UniversalSource X) =
        Subgroup.normalClosure
          ({universalDefect X} : Set (UniversalSource X)) := by
  letI : Countable X := Finite.to_countable
  letI : Countable (FreeGroup X) := freeGroupCountable
  have hFree : IsOperatorMF (FreeGroup X) :=
    isOperatorMF_of_residuallyFinite
  have hrad := exact_radical_of_visible_mf (FreeGroup X) hFree
  exact ⟨universal_source_isFinitelyPresented X, hFree, hrad.2.2,
    MFCamouflage.Hotel.camouflage_defect_ne_one _,
    hrad.1.trans hrad.2.1⟩

/-- The universal hidden switch has its advertised compiler behavior: adding
the single relation `universalDefect X = 1` recovers the visible free group. -/
theorem universal_defect_quotient_equiv (X : Type) :
    Nonempty
      (UniversalSource X ⧸
          Subgroup.normalClosure
            ({universalDefect X} : Set (UniversalSource X))
        ≃* FreeGroup X) :=
  defect_quotient_equiv (FreeGroup X)

/-! ## Stability-preserving surgery -/

/-- **Stability theorem.**  Invisible extension preserves point-norm
matricial stability in both directions. -/
theorem extension_stable_iff
    (Q : Type) [Group Q] :
    IsPointNormMatriciallyStable (Extension Q) ↔
      IsPointNormMatriciallyStable Q :=
  MFCamouflage.Hotel.isPointNormMatriciallyStable_camouflage_iff Q

/-- The fixed source over any generator type is stable, since free groups are
point-norm matricially stable. -/
theorem universal_source_isPointNormMatriciallyStable (X : Type) :
    IsPointNormMatriciallyStable (UniversalSource X) :=
  (extension_stable_iff (FreeGroup X)).mpr
    (freeGroup_isPointNormMatriciallyStable X)

/-- **A finitely presented, point-norm matricially stable, non-MF group.**
The cyclic camouflage has exact one-word MF radical while stability is
transported from the integers. -/
theorem stable_nonMF_invisible_extension_exists :
    ∃ (G : Type) (_ : Group G) (d : G),
      Group.IsFinitelyPresented G ∧
        IsPointNormMatriciallyStable G ∧
        ¬ IsOperatorMF G ∧
        d ≠ 1 ∧
        normMFResidual G =
          Subgroup.normalClosure ({d} : Set G) := by
  refine ⟨Extension (Multiplicative ℤ), inferInstance,
    defect (Multiplicative ℤ),
    extension_isFinitelyPresented (Multiplicative ℤ),
    (extension_stable_iff (Multiplicative ℤ)).mpr
      multiplicativeInt_isPointNormMatriciallyStable, ?_,
    MFCamouflage.Hotel.camouflage_defect_ne_one _, ?_⟩
  · exact MFCamouflage.Hotel.not_isOperatorMF _
      LiteralLEFExtension.integerQuotient_isOperatorMF
  · have hrad := exact_radical_of_visible_mf (Multiplicative ℤ)
      LiteralLEFExtension.integerQuotient_isOperatorMF
    exact hrad.1.trans hrad.2.1

end InvisibleExtensions
end GroupApproximation
