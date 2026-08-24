import GroupApproximation.Leavitt.HilbertHotelEndpoint
import GroupApproximation.Sofic.MFCamouflage
import GroupApproximation.Sofic.MFRelationClosure

/-!
# MF radical and semantic closure under camouflage

The algebraic compiler in `Sofic.MFCamouflage` becomes an MF compiler when
the black-hole vertex has full genuine-corona radical.  This file proves the
exact pullback formula for the radical, then upgrades it to the entire closure
operator on normal subgroups.  The final namespace instantiates the abstract
results with Cairn's unconditional Hilbert-hotel cover and its one normally
generating defect.
-/

namespace GroupApproximation
namespace MFCamouflage

noncomputable section

variable {B Q : Type} [Group B] [Group Q]

/-- Full radical means that every genuine matrix-corona homomorphism out of
the black-hole group is trivial. -/
theorem actualCoronaHom_eq_one_of_residual_eq_top
    (hfull : actualCoronaMFResidual B = ⊤)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ f : B →* unitary (NormMatrixCStarCorona (fun n ↦ X n)), f = 1 := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro f
  apply MonoidHom.ext
  intro b
  have hb : b ∈ actualCoronaMFResidual B := by
    rw [hfull]
    exact Subgroup.mem_top b
  exact hb X hX f

/-- The projection kernel is invisible in every genuine matrix corona.  This
does not need normal generation: full invisibility of the entire `B` vertex
already forces every representation to factor through the projection. -/
theorem projection_ker_le_actualCoronaMFResidual (d : B) (Q : Type)
    [Group Q] (hfull : actualCoronaMFResidual B = ⊤) :
    (projection d Q).ker ≤ actualCoronaMFResidual (Camouflage d Q) := by
  intro x hx X hX
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  have hkill : rho.comp (blackHole d Q) = 1 :=
    actualCoronaHom_eq_one_of_residual_eq_top hfull X hX _
  have hfactor := factor_through_projection d Q rho hkill
  have heval := DFunLike.congr_fun hfactor x
  have hx1 := MonoidHom.mem_ker.mp hx
  change rho (visible d Q (projection d Q x)) = rho x at heval
  rw [hx1, map_one, map_one] at heval
  exact heval.symm

/-- **Exact MF radical transplantation.**  The radical of the camouflage
group is the inverse image of the radical of its visible quotient. -/
theorem actualCoronaMFResidual_eq_comap (d : B) (Q : Type) [Group Q]
    (hfull : actualCoronaMFResidual B = ⊤) :
    actualCoronaMFResidual (Camouflage d Q) =
      (actualCoronaMFResidual Q).comap (projection d Q) := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_comap.mpr
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro sigma
    exact hx X hX (sigma.comp (projection d Q))
  · intro x hx X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    have hkill : rho.comp (blackHole d Q) = 1 :=
      actualCoronaHom_eq_one_of_residual_eq_top hfull X hX _
    let sigma : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
      rho.comp (visible d Q)
    have hfactor := factor_through_projection d Q rho hkill
    have heval := DFunLike.congr_fun hfactor x
    exact heval.symm.trans ((Subgroup.mem_comap.mp hx) X hX sigma)

/-- If the visible quotient is MF, the radical is exactly the projection
kernel. -/
theorem actualCoronaMFResidual_eq_ker (d : B) (Q : Type) [Group Q]
    [Countable Q] (hfull : actualCoronaMFResidual B = ⊤)
    (hQ : IsCDEOperatorMF Q) :
    actualCoronaMFResidual (Camouflage d Q) = (projection d Q).ker := by
  rw [actualCoronaMFResidual_eq_comap d Q hfull,
    (isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hQ)]
  rfl

/-- Precomposition is a bijection for every genuine norm-matrix-corona
target, at every positive dimension sequence. -/
theorem actualCorona_precomp_bijective (d : B) (Q : Type) [Group Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (fun f : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        f.comp (projection d Q)) := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  exact precomp_bijective d Q
    (actualCoronaHom_eq_one_of_residual_eq_top hfull X hX)

/-- Every CDE/operator-MF target is invisible to the black-hole vertex, so
the projection is the reflection map on all such targets. -/
theorem cdeMF_precomp_bijective
    (d : B) (Q : Type) [Group Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    {T : Type} [Group T] [Countable T] (hT : IsCDEOperatorMF T) :
    Function.Bijective (fun f : Q →* T ↦ f.comp (projection d Q)) := by
  obtain ⟨dims, hdims, _hmono, j, hj⟩ := hT
  apply precomp_bijective d Q
  intro f
  ext b
  apply hj
  have htrivial : j.comp f = 1 :=
    actualCoronaHom_eq_one_of_residual_eq_top hfull
      (fun n ↦ naturalFiniteModel (dims n)) (by simpa using hdims) _
  simpa using DFunLike.congr_fun htrivial b

/-- Equivalent operator-MF spelling of the reflection theorem. -/
theorem operatorMF_precomp_bijective
    (d : B) (Q : Type) [Group Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    {T : Type} [Group T] [Countable T] (hT : IsOperatorMF T) :
    Function.Bijective (fun f : Q →* T ↦ f.comp (projection d Q)) :=
  cdeMF_precomp_bijective d Q hfull
    ((isCDEOperatorMF_iff_isOperatorMF T).mpr hT)

/-- Normality of the direct image used by semantic closure transplantation. -/
instance mapProjection_normal (d : B) (Q : Type) [Group Q]
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    (N.map (projection d Q)).Normal :=
  Subgroup.Normal.map inferInstance (projection d Q)
    (projection_surjective d Q)

/-- **MF semantic-closure transplantation.**  Every MF consequence of every
normal relation set is pulled back from the visible quotient. -/
theorem actualCoronaMFClosure_eq_comap (d : B) (Q : Type) [Group Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    actualCoronaMFClosure N =
      (actualCoronaMFClosure (N.map (projection d Q))).comap
        (projection d Q) := by
  ext x
  constructor
  · intro hx
    apply Subgroup.mem_comap.mpr
    rw [mem_actualCoronaMFClosure_iff]
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro sigma hkill
    rw [mem_actualCoronaMFClosure_iff] at hx
    exact hx X hX (sigma.comp (projection d Q)) (by
      intro y hy
      exact hkill (projection d Q y) ⟨y, hy, rfl⟩)
  · intro hx
    rw [Subgroup.mem_comap, mem_actualCoronaMFClosure_iff] at hx
    rw [mem_actualCoronaMFClosure_iff]
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho hkillN
    have hkillB : rho.comp (blackHole d Q) = 1 :=
      actualCoronaHom_eq_one_of_residual_eq_top hfull X hX _
    let sigma : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
      rho.comp (visible d Q)
    have hfactor := factor_through_projection d Q rho hkillB
    have hkillMap : ∀ y ∈ N.map (projection d Q), sigma y = 1 := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have heval := DFunLike.congr_fun hfactor z
      exact heval.trans (hkillN z hz)
    have hvisible := hx X hX sigma hkillMap
    have heval := DFunLike.congr_fun hfactor x
    exact heval.symm.trans hvisible

local instance camouflageQuotientCountable
    (d : B) (Q : Type) [Group Q] [Countable B] [Countable Q]
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    Countable (Camouflage d Q ⧸ N) :=
  Function.Surjective.countable (QuotientGroup.mk'_surjective N)

local instance visibleQuotientCountable
    (d : B) (Q : Type) [Group Q] [Countable Q]
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    Countable (Q ⧸ N.map (projection d Q)) :=
  Function.Surjective.countable
    (QuotientGroup.mk'_surjective (N.map (projection d Q)))

/-- A quotient of the camouflage group is MF exactly when it kills the hidden
kernel and its visible quotient is MF. -/
theorem quotient_isCDEOperatorMF_iff (d : B) (Q : Type) [Group Q]
    [Countable B] [Countable Q]
    (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (Camouflage d Q)) [N.Normal] :
    IsCDEOperatorMF (Camouflage d Q ⧸ N) ↔
      (projection d Q).ker ≤ N ∧
        IsCDEOperatorMF (Q ⧸ N.map (projection d Q)) := by
  constructor
  · intro hMF
    have hclosed : actualCoronaMFClosure N = N :=
      (actualCoronaMFClosure_eq_self_iff N).mpr hMF
    have htransport := actualCoronaMFClosure_eq_comap d Q hfull N
    have hcomap :
        (actualCoronaMFClosure (N.map (projection d Q))).comap
            (projection d Q) = N := by
      rw [← htransport, hclosed]
    constructor
    · intro x hx
      rw [← hcomap]
      apply Subgroup.mem_comap.mpr
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _
    · apply (actualCoronaMFClosure_eq_self_iff
          (N.map (projection d Q))).mp
      have hmap := congrArg
        (fun K : Subgroup (Camouflage d Q) ↦ K.map (projection d Q)) hcomap
      simpa [Subgroup.map_comap_eq_self_of_surjective
          (projection_surjective d Q)] using hmap
  · rintro ⟨hker, hMF⟩
    apply (actualCoronaMFClosure_eq_self_iff N).mp
    rw [actualCoronaMFClosure_eq_comap d Q hfull N,
      (actualCoronaMFClosure_eq_self_iff
        (N.map (projection d Q))).mpr hMF]
    exact Subgroup.comap_map_eq_self hker

end

/-! ## The unconditional Hilbert-hotel instance -/

namespace Hotel

open HilbertHotel

/-- Cairn's existing finitely presented full-radical seed. -/
abbrev BlackHole : Type := CoverBlock.HotelGroup

/-- The one normally generating compression defect of the seed. -/
noncomputable abbrev sourceDefect : BlackHole :=
  CoverBlock.blockDefect CoverBlock.blockCoverInputs
    CoverBlock.coverBlockResiduals

/-- The concrete camouflage compiler built from the Hilbert-hotel seed. -/
noncomputable abbrev Camouflage (Q : Type) [Group Q] : Type :=
  MFCamouflage.Camouflage sourceDefect Q

theorem sourceDefect_ne_one : sourceDefect ≠ 1 :=
  CoverBlock.blockDefect_ne_one CoverBlock.blockCoverInputs
    CoverBlock.coverBlockResiduals

theorem sourceDefect_normallyGenerates :
    Subgroup.normalClosure ({sourceDefect} : Set BlackHole) = ⊤ :=
  Endpoint.hotelGroup_defect_normallyGenerates

theorem source_actualCoronaMFResidual_eq_top :
    actualCoronaMFResidual BlackHole = ⊤ := by
  rw [actualCoronaMFResidual_eq_coronaMFResidual]
  exact Endpoint.hotelGroup_coronaMFResidual_eq_top

theorem camouflage_defect_ne_one (Q : Type) [Group Q] :
    MFCamouflage.defect sourceDefect Q ≠ 1 :=
  MFCamouflage.defect_ne_one sourceDefect Q sourceDefect_ne_one

theorem projection_ker_eq_normalClosure (Q : Type) [Group Q] :
    (MFCamouflage.projection sourceDefect Q).ker =
      Subgroup.normalClosure
        ({MFCamouflage.defect sourceDefect Q} : Set (Camouflage Q)) :=
  MFCamouflage.projection_ker_eq_normalClosure sourceDefect Q
    sourceDefect_normallyGenerates

theorem actualCoronaMFResidual_eq_comap (Q : Type) [Group Q] :
    actualCoronaMFResidual (Camouflage Q) =
      (actualCoronaMFResidual Q).comap
        (MFCamouflage.projection sourceDefect Q) :=
  MFCamouflage.actualCoronaMFResidual_eq_comap sourceDefect Q
    source_actualCoronaMFResidual_eq_top

/-- **Full MF-semantic closure formula for the prescribed-quotient
construction.**  For every normal relation subgroup `N` of `W_Q`, its MF
root is exactly the inverse image of the MF root of its prescribed image in
`Q`. -/
theorem actualCoronaMFClosure_eq_comap
    (Q : Type) [Group Q]
    (N : Subgroup (Camouflage Q)) [N.Normal] :
    actualCoronaMFClosure N =
      (actualCoronaMFClosure
        (N.map (MFCamouflage.projection sourceDefect Q))).comap
          (MFCamouflage.projection sourceDefect Q) :=
  MFCamouflage.actualCoronaMFClosure_eq_comap sourceDefect Q
    source_actualCoronaMFResidual_eq_top N

theorem actualCoronaMFResidual_eq_normalClosure
    (Q : Type) [Group Q] [Countable Q] (hQ : IsCDEOperatorMF Q) :
    actualCoronaMFResidual (Camouflage Q) =
      Subgroup.normalClosure
        ({MFCamouflage.defect sourceDefect Q} : Set (Camouflage Q)) := by
  rw [MFCamouflage.actualCoronaMFResidual_eq_ker sourceDefect Q
      source_actualCoronaMFResidual_eq_top hQ,
    projection_ker_eq_normalClosure]

/-- The compiler output is not MF whenever the visible group is MF: its
nontrivial distinguished relation lies in the exact MF radical. -/
theorem not_isCDEOperatorMF
    (Q : Type) [Group Q] [Countable Q] (hQ : IsCDEOperatorMF Q) :
    ¬ IsCDEOperatorMF (Camouflage Q) := by
  intro hW
  have hbot : actualCoronaMFResidual (Camouflage Q) = ⊥ :=
    (isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hW)
  have hmem : MFCamouflage.defect sourceDefect Q ∈
      actualCoronaMFResidual (Camouflage Q) := by
    rw [actualCoronaMFResidual_eq_normalClosure Q hQ]
    exact Subgroup.subset_normalClosure (Set.mem_singleton _)
  rw [hbot] at hmem
  exact camouflage_defect_ne_one Q (Subgroup.mem_bot.mp hmem)

theorem not_isOperatorMF
    (Q : Type) [Group Q] [Countable Q] (hQ : IsOperatorMF Q) :
    ¬ IsOperatorMF (Camouflage Q) := by
  rw [← isCDEOperatorMF_iff_isOperatorMF]
  exact not_isCDEOperatorMF Q
    ((isCDEOperatorMF_iff_isOperatorMF Q).mpr hQ)

/-- The concrete projection is the reflection arrow into every countable
operator-MF target. -/
theorem operatorMF_precomp_bijective
    (Q : Type) [Group Q] {T : Type} [Group T] [Countable T]
    (hT : IsOperatorMF T) :
    Function.Bijective
      (fun f : Q →* T ↦
        f.comp (MFCamouflage.projection sourceDefect Q)) :=
  MFCamouflage.operatorMF_precomp_bijective sourceDefect Q
    source_actualCoronaMFResidual_eq_top hT

theorem isFinitelyPresented (Q : Type) [Group Q]
    [Group.IsFinitelyPresented Q] :
    Group.IsFinitelyPresented (Camouflage Q) :=
  MFCamouflage.isFinitelyPresented sourceDefect Q

end Hotel
end MFCamouflage
end GroupApproximation
