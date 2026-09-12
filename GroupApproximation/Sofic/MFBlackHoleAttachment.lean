import GroupApproximation.Higman.AmalgamPushout
import GroupApproximation.Sofic.FullMFRadicalClosurePullback
import GroupApproximation.Sofic.MFCamouflageRadical

/-!
# MF-invisible relation cells

Let `B` be a black-hole group, let `left : C →* B`, and attach it to a group
`G` along `right : C →* G`.  The amalgam `B *_C G` has a canonical map to

`G / normalClosure(range right)`.

Every target which sees only the trivial representation of `B` sees this map
as an equivalence on homomorphism sets.  For a full-MF-radical `B`, this gives
the exact semantic relation gadget: all MF representations impose the edge
relations although those relations remain algebraically nontrivial when the
two edge maps are injective.
-/

namespace GroupApproximation
namespace MFBlackHoleAttachment

open Monoid

variable {B C G : Type} [Group B] [Group C] [Group G]

/-- The black-hole attachment `B *_C G`. -/
abbrev Attachment (left : C →* B) (right : C →* G) : Type :=
  Higman.Amalgam.Push left right

/-- Inclusion of the black-hole vertex. -/
abbrev blackHole (left : C →* B) (right : C →* G) :
    B →* Attachment left right :=
  PushoutI.of (φ := Higman.Amalgam.famHom left right) false

/-- Inclusion of the visible vertex. -/
abbrev visible (left : C →* B) (right : C →* G) :
    G →* Attachment left right :=
  PushoutI.of (φ := Higman.Amalgam.famHom left right) true

/-- The relations semantically imposed on the visible vertex. -/
def imposedRelations (right : C →* G) : Subgroup G :=
  Subgroup.normalClosure (Set.range right)

instance imposedRelations_normal (right : C →* G) :
    (imposedRelations right).Normal :=
  Subgroup.normalClosure_normal

/-- The visible quotient after imposing the attached edge relations. -/
abbrev VisibleQuotient (right : C →* G) : Type :=
  G ⧸ imposedRelations right

/-- The quotient map on the visible vertex. -/
abbrev visibleQuotientMk (right : C →* G) :
    G →* VisibleQuotient right :=
  QuotientGroup.mk' (imposedRelations right)

/-- The two vertex maps defining the semantic quotient. -/
def projectionFamily (_left : C →* B) (right : C →* G) :
    ∀ b, Higman.Amalgam.fam B G b →* VisibleQuotient right
  | false => 1
  | true => visibleQuotientMk right

/-- The black-hole attachment projects onto the quotient in which the edge
image in `G` is algebraically killed. -/
def projection (left : C →* B) (right : C →* G) :
    Attachment left right →* VisibleQuotient right := by
  refine PushoutI.lift (projectionFamily left right)
    (1 : C →* VisibleQuotient right) ?_
  intro b
  cases b with
  | false => rfl
  | true =>
      ext c
      change (visibleQuotientMk right) (right c) = 1
      apply (QuotientGroup.eq_one_iff (right c)).mpr
      exact Subgroup.subset_normalClosure ⟨c, rfl⟩

@[simp] theorem projection_blackHole
    (left : C →* B) (right : C →* G) (b : B) :
    projection left right (blackHole left right b) = 1 := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem projection_visible
    (left : C →* B) (right : C →* G) (g : G) :
    projection left right (visible left right g) = visibleQuotientMk right g := by
  exact PushoutI.lift_of _ _ _ _

/-- The two copies of an edge element agree in the amalgam. -/
theorem visible_right_eq_blackHole_left
    (left : C →* B) (right : C →* G) (c : C) :
    visible left right (right c) = blackHole left right (left c) := by
  calc
    visible left right (right c) =
        PushoutI.base (Higman.Amalgam.famHom left right) c :=
      PushoutI.of_apply_eq_base
        (Higman.Amalgam.famHom left right) true c
    _ = blackHole left right (left c) :=
      (PushoutI.of_apply_eq_base
        (Higman.Amalgam.famHom left right) false c).symm

/-- The semantic projection is onto. -/
theorem projection_surjective
    (left : C →* B) (right : C →* G) :
    Function.Surjective (projection left right) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (imposedRelations right) q
  exact ⟨visible left right g, projection_visible left right g⟩

section Target

variable {T : Type} [Monoid T]

/-- A map out of the attachment factors through the semantic quotient as soon
as it kills the black-hole vertex. -/
theorem exists_factor_through_projection
    (left : C →* B) (right : C →* G)
    (theta : Attachment left right →* T)
    (hkill : theta.comp (blackHole left right) = 1) :
    ∃ psi : VisibleQuotient right →* T,
      psi.comp (projection left right) = theta := by
  let thetaG : G →* T := theta.comp (visible left right)
  have hrelations : imposedRelations right ≤ thetaG.ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨c, rfl⟩
    apply MonoidHom.mem_ker.mpr
    change theta (visible left right (right c)) = 1
    rw [visible_right_eq_blackHole_left]
    exact DFunLike.congr_fun hkill (left c)
  let psi : VisibleQuotient right →* T :=
    QuotientGroup.lift (imposedRelations right) thetaG hrelations
  refine ⟨psi, ?_⟩
  refine PushoutI.hom_ext_nonempty (fun b ↦ ?_)
  cases b with
  | false =>
      ext b
      change psi (projection left right (blackHole left right b)) =
        theta (blackHole left right b)
      rw [projection_blackHole, map_one]
      exact (DFunLike.congr_fun hkill b).symm
  | true =>
      ext g
      change psi (projection left right (visible left right g)) =
        thetaG g
      rw [projection_visible]
      exact QuotientGroup.lift_mk' (imposedRelations right) hrelations g

/-- **Black-hole attachment factorization.**  If every map from `B` to `T`
is trivial, precomposition with the semantic projection is a bijection. -/
theorem precomp_bijective
    (left : C →* B) (right : C →* G)
    (hB : ∀ f : B →* T, f = 1) :
    Function.Bijective
      (fun psi : VisibleQuotient right →* T ↦
        psi.comp (projection left right)) := by
  constructor
  · intro psi₁ psi₂ h
    apply MonoidHom.ext
    intro q
    obtain ⟨x, hx⟩ := projection_surjective left right q
    have heval := DFunLike.congr_fun h x
    simpa only [MonoidHom.comp_apply, hx] using heval
  · intro theta
    exact exists_factor_through_projection left right theta
      (hB (theta.comp (blackHole left right)))

end Target

/-- Full MF radical of `B` makes the semantic projection an equivalence on
homomorphisms into every countable operator-MF target. -/
theorem operatorMF_precomp_bijective
    (left : C →* B) (right : C →* G)
    (hfull : actualCoronaMFResidual B = ⊤)
    {T : Type} [Group T] [Countable T] (hT : IsOperatorMF T) :
    Function.Bijective
      (fun psi : VisibleQuotient right →* T ↦
        psi.comp (projection left right)) := by
  obtain ⟨dims, hdims, _hmono, j, hj⟩ :=
    (isCDEOperatorMF_iff_isOperatorMF T).mpr hT
  apply precomp_bijective left right
  intro f
  ext b
  apply hj
  have htrivial : j.comp f = 1 :=
    MFCamouflage.actualCoronaHom_eq_one_of_residual_eq_top hfull
      (fun n ↦ naturalFiniteModel (dims n)) (by simpa using hdims) _
  simpa using DFunLike.congr_fun htrivial b

/-- The kernel of the semantic projection is invisible to every genuine
norm-matrix-corona representation. -/
theorem projection_ker_le_actualCoronaMFResidual
    (left : C →* B) (right : C →* G)
    (hfull : actualCoronaMFResidual B = ⊤) :
    (projection left right).ker ≤
      actualCoronaMFResidual (Attachment left right) := by
  intro x hx X hX
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  have hkill : rho.comp (blackHole left right) = 1 :=
    MFCamouflage.actualCoronaHom_eq_one_of_residual_eq_top hfull X hX _
  obtain ⟨psi, hpsi⟩ :=
    exists_factor_through_projection left right rho hkill
  have heval := DFunLike.congr_fun hpsi x
  rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one] at heval
  exact heval.symm

/-- **Exact MF radical of a black-hole attachment.** -/
theorem actualCoronaMFResidual_eq_comap
    (left : C →* B) (right : C →* G)
    (hfull : actualCoronaMFResidual B = ⊤) :
    actualCoronaMFResidual (Attachment left right) =
      (actualCoronaMFResidual (VisibleQuotient right)).comap
        (projection left right) :=
  actualCoronaMFResidual_eq_comap_of_surjective_of_ker_le
    (projection left right) (projection_surjective left right)
    (projection_ker_le_actualCoronaMFResidual left right hfull)

/-- Normality of the direct image along the surjective semantic projection. -/
instance mapProjection_normal
    (left : C →* B) (right : C →* G)
    (N : Subgroup (Attachment left right)) [N.Normal] :
    (N.map (projection left right)).Normal :=
  Subgroup.Normal.map inferInstance (projection left right)
    (projection_surjective left right)

/-- Every MF semantic closure in the attachment is pulled back from the
visible semantic quotient. -/
theorem actualCoronaMFClosure_eq_comap
    (left : C →* B) (right : C →* G)
    (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (Attachment left right)) [N.Normal] :
    actualCoronaMFClosure N =
      (actualCoronaMFClosure
        (N.map (projection left right))).comap (projection left right) :=
  actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le
    (projection left right) (projection_surjective left right)
    (projection_ker_le_actualCoronaMFResidual left right hfull) N

/-- The projection kernel is the normal closure of the black-hole vertex. -/
theorem projection_ker_eq_normalClosure_blackHole
    (left : C →* B) (right : C →* G) :
    (projection left right).ker =
      Subgroup.normalClosure (Set.range (blackHole left right)) := by
  let K := Subgroup.normalClosure (Set.range (blackHole left right))
  apply le_antisymm
  · intro x hx
    let qK : Attachment left right →* (Attachment left right ⧸ K) :=
      QuotientGroup.mk' K
    have hkill : qK.comp (blackHole left right) = 1 := by
      ext b
      apply (QuotientGroup.eq_one_iff (blackHole left right b)).mpr
      exact Subgroup.subset_normalClosure ⟨b, rfl⟩
    obtain ⟨psi, hpsi⟩ :=
      exists_factor_through_projection left right qK hkill
    apply (QuotientGroup.eq_one_iff x).mp
    have heval := DFunLike.congr_fun hpsi x
    rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one] at heval
    exact heval.symm
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨b, rfl⟩
    exact MonoidHom.mem_ker.mpr (projection_blackHole left right b)

/-- If one edge element normally generates `B`, the whole hidden kernel is
normally generated by its one image in the attachment. -/
theorem projection_ker_eq_normalClosure_one
    (left : C →* B) (right : C →* G) (c : C)
    (hgen : Subgroup.normalClosure ({left c} : Set B) = ⊤) :
    (projection left right).ker =
      Subgroup.normalClosure
        ({blackHole left right (left c)} : Set (Attachment left right)) := by
  rw [projection_ker_eq_normalClosure_blackHole]
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨b, rfl⟩
    have hb : b ∈ Subgroup.normalClosure ({left c} : Set B) := by
      rw [hgen]
      exact Subgroup.mem_top b
    let K := Subgroup.normalClosure
      ({blackHole left right (left c)} : Set (Attachment left right))
    have hle : Subgroup.normalClosure ({left c} : Set B) ≤
        K.comap (blackHole left right) := by
      refine Subgroup.normalClosure_le_normal
        (Set.singleton_subset_iff.mpr ?_)
      exact Subgroup.subset_normalClosure (Set.mem_singleton _)
    exact hle hb
  · refine Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr ?_)
    exact Subgroup.subset_normalClosure ⟨left c, rfl⟩

/-- If the visible semantic quotient has trivial MF radical and one edge
element normally generates the black hole, the attachment's exact MF radical
is the normal closure of that single surviving relation cell. -/
theorem actualCoronaMFResidual_eq_normalClosure_one
    (left : C →* B) (right : C →* G)
    (hfull : actualCoronaMFResidual B = ⊤)
    (hvisible :
      actualCoronaMFResidual (VisibleQuotient right) = ⊥)
    (c : C) (hgen : Subgroup.normalClosure ({left c} : Set B) = ⊤) :
    actualCoronaMFResidual (Attachment left right) =
      Subgroup.normalClosure
        ({blackHole left right (left c)} : Set (Attachment left right)) := by
  rw [actualCoronaMFResidual_eq_comap left right hfull, hvisible]
  change (projection left right).ker = _
  exact projection_ker_eq_normalClosure_one left right c hgen

/-- If both edge maps are injective, both vertices embed and every nontrivial
attached edge element remains nontrivial algebraically. -/
theorem edge_survives
    (left : C →* B) (right : C →* G)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (c : C) (hc : left c ≠ 1) :
    blackHole left right (left c) ≠ 1 := by
  intro h
  have hinj := Higman.Amalgam.of_injective_push left right hleft hright false
  apply hc
  apply hinj
  exact h.trans (map_one (blackHole left right)).symm

/-- Finite presentation is preserved for a finite attachment over a finitely
generated edge group. -/
theorem isFinitelyPresented
    (left : C →* B) (right : C →* G)
    [Group.IsFinitelyPresented B] [Group.IsFinitelyPresented G] [Group.FG C] :
    Group.IsFinitelyPresented (Attachment left right) :=
  Higman.Amalgam.isFinitelyPresented_push left right

end MFBlackHoleAttachment
end GroupApproximation
