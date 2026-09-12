import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceMFCamouflageClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.PrescribedQuotients

/-!
# Completion of the printed camouflage route

Sentence wrappers for census rows 278--294.  Row 278 is imported from
`SentenceMFCamouflageClosure`; the declarations below continue from its two
restriction identities through factorization, MF-radical transplantation, and
the closing relation calculus.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

variable {B : Type} [Group B] {Q : Type} [Group Q]

local instance sentence293CamouflageQuotientCountable
    (d : B) [Countable B] [Countable Q]
    (N : Subgroup (MFCamouflage.Camouflage d Q)) [hN : N.Normal] :
    Countable (MFCamouflage.Camouflage d Q ⧸ N) :=
  Function.Surjective.countable
    (@QuotientGroup.mk'_surjective
      (MFCamouflage.Camouflage d Q) _ N hN)

local instance sentence293VisibleQuotientCountable
    (d : B) [Countable Q]
    (N : Subgroup (MFCamouflage.Camouflage d Q)) [N.Normal] :
    Countable (Q ⧸ N.map (MFCamouflage.projection d Q)) :=
  Function.Surjective.countable
    (QuotientGroup.mk'_surjective
      (N.map (MFCamouflage.projection d Q)))

/-- **Sentence 279.**  On the product vertex, the edge coordinate is killed,
so `f(q,a)=f(q,1)f(1,a)=f(q,1)`. -/
theorem manuscriptSentence279_productVertex_factorization
    {T : Type} [Group T] (d : B)
    (f : MFCamouflage.Camouflage d Q →* T)
    (hkill : f.comp (MFCamouflage.blackHole d Q) = 1)
    (x : Q × MFCamouflage.Edge d) :
    f (MFCamouflage.productVertex d Q x) =
        f (MFCamouflage.visible d Q x.1) *
          f (MFCamouflage.blackHole d Q x.2.1) ∧
      f (MFCamouflage.productVertex d Q x) =
        f (MFCamouflage.visible d Q x.1) := by
  have hedge : f (MFCamouflage.blackHole d Q x.2.1) = 1 :=
    DFunLike.congr_fun hkill x.2.1
  constructor
  · rw [MFCamouflage.productVertex_eq_visible_mul_blackHole, map_mul]
  · rw [MFCamouflage.productVertex_eq_visible_mul_blackHole, map_mul,
      hedge, mul_one]

/-- **Sentences 280--281.**  Killing the black-hole restriction makes the
restriction to `Q×A`, and then the whole amalgam map, factor through `π_Q`. -/
theorem manuscriptSentences280_281_factorThroughProjection
    {T : Type} [Group T] (d : B)
    (f : MFCamouflage.Camouflage d Q →* T)
    (hkill : f.comp (MFCamouflage.blackHole d Q) = 1) :
    (f.comp (MFCamouflage.visible d Q)).comp
        (MFCamouflage.projection d Q) = f :=
  MFCamouflage.factor_through_projection d Q f hkill

/-- **Sentence 282.**  The factor is unique because the projection is
surjective. -/
theorem manuscriptSentence282_factor_unique
    {T : Type} [Group T] (d : B) {g h : Q →* T}
    (heq : g.comp (MFCamouflage.projection d Q) =
      h.comp (MFCamouflage.projection d Q)) :
    g = h := by
  ext q
  obtain ⟨x, rfl⟩ := MFCamouflage.projection_surjective d Q q
  exact DFunLike.congr_fun heq x

/-- **Sentence 283.**  The distinguished element belongs to the projection
kernel. -/
theorem manuscriptSentence283_defect_mem_kernel (d : B) :
    MFCamouflage.defect d Q ∈ (MFCamouflage.projection d Q).ker :=
  MonoidHom.mem_ker.mpr (MFCamouflage.projection_blackHole d Q d)

/-- **Sentence 284.**  Quotienting by the normally generating distinguished
relation has exactly the projection kernel, leaving the visible quotient. -/
theorem manuscriptSentence284_quotientKernel
    (d : B) (hgen : Subgroup.normalClosure ({d} : Set B) = ⊤) :
    (MFCamouflage.projection d Q).ker =
      Subgroup.normalClosure
        ({MFCamouflage.defect d Q} : Set (MFCamouflage.Camouflage d Q)) :=
  MFCamouflage.projection_ker_eq_normalClosure d Q hgen

/-- **Sentence 285.**  Full actual corona MF radical makes every corona map
from the black-hole vertex trivial. -/
theorem manuscriptSentence285_blackHoleCoronaHom_eq_one
    (hfull : actualCoronaMFResidual B = ⊤)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ f : B →* unitary (NormMatrixCStarCorona (fun n ↦ X n)), f = 1 :=
  MFCamouflage.actualCoronaHom_eq_one_of_residual_eq_top hfull X hX

/-- **Sentence 286.**  Universal factorization is a bijection for every
countable MF target. -/
theorem manuscriptSentence286_MFTarget_precomp_bijective
    (d : B) (hfull : actualCoronaMFResidual B = ⊤)
    {T : Type} [Group T] [Countable T] (hT : IsCDEOperatorMF T) :
    Function.Bijective
      (fun f : Q →* T ↦ f.comp (MFCamouflage.projection d Q)) :=
  MFCamouflage.cdeMF_precomp_bijective d Q hfull hT

/-- **Sentence 287.**  The same unique factorization holds for every genuine
norm-matrix-corona target. -/
theorem manuscriptSentence287_corona_precomp_bijective
    (d : B) (hfull : actualCoronaMFResidual B = ⊤)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (fun f : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) ↦
        f.comp (MFCamouflage.projection d Q)) :=
  MFCamouflage.actualCorona_precomp_bijective d Q hfull X hX

/-- **Sentence 288.**  Intersecting the uniquely corresponding kernels gives
the radical pullback formula. -/
theorem manuscriptSentence288_radicalPullback
    (d : B) (hfull : actualCoronaMFResidual B = ⊤) :
    actualCoronaMFResidual (MFCamouflage.Camouflage d Q) =
      (actualCoronaMFResidual Q).comap (MFCamouflage.projection d Q) :=
  MFCamouflage.actualCoronaMFResidual_eq_comap d Q hfull

/-- **Sentence 289.**  The projection kernel is radical-invisible and contains
the surviving defect; hence the camouflage group is not MF. -/
theorem manuscriptSentence289_camouflage_not_MF
    [Countable B] [Countable Q] (d : B)
    (hfull : actualCoronaMFResidual B = ⊤) (hd : d ≠ 1) :
    (MFCamouflage.projection d Q).ker ≤
        actualCoronaMFResidual (MFCamouflage.Camouflage d Q) ∧
      MFCamouflage.defect d Q ∈
        actualCoronaMFResidual (MFCamouflage.Camouflage d Q) ∧
      ¬ IsCDEOperatorMF (MFCamouflage.Camouflage d Q) := by
  have hker := MFCamouflage.projection_ker_le_actualCoronaMFResidual
    d Q hfull
  have hdefect := hker (manuscriptSentence283_defect_mem_kernel (Q := Q) d)
  refine ⟨hker, hdefect, ?_⟩
  intro hMF
  have hbot := isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hMF
  rw [hbot] at hdefect
  exact MFCamouflage.defect_ne_one d Q hd (Subgroup.mem_bot.mp hdefect)

/-- **Sentence 290.**  If `Q` is MF, the camouflage radical is the projection
kernel and therefore the normal closure of the distinguished defect. -/
theorem manuscriptSentence290_radical_eq_kernel_eq_normalClosure
    [Countable Q] (d : B) (hfull : actualCoronaMFResidual B = ⊤)
    (hQ : IsCDEOperatorMF Q)
    (hgen : Subgroup.normalClosure ({d} : Set B) = ⊤) :
    actualCoronaMFResidual (MFCamouflage.Camouflage d Q) =
        (MFCamouflage.projection d Q).ker ∧
      (MFCamouflage.projection d Q).ker =
        Subgroup.normalClosure
          ({MFCamouflage.defect d Q} : Set (MFCamouflage.Camouflage d Q)) :=
  ⟨MFCamouflage.actualCoronaMFResidual_eq_ker d Q hfull hQ,
    MFCamouflage.projection_ker_eq_normalClosure d Q hgen⟩

/-- **Sentence 291.**  MF semantic closure is pulled back from the visible
quotient. -/
theorem manuscriptSentence291_closurePullback
    (d : B) (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (MFCamouflage.Camouflage d Q)) [N.Normal] :
    actualCoronaMFClosure N =
      (actualCoronaMFClosure
        (N.map (MFCamouflage.projection d Q))).comap
          (MFCamouflage.projection d Q) :=
  MFCamouflage.actualCoronaMFClosure_eq_comap d Q hfull N

/-- **Sentence 292.**  A factored target map kills `N` exactly when its
visible factor kills `π_Q(N)`. -/
theorem manuscriptSentence292_factoredMap_kills_iff
    (d : B) {T : Type} [Group T]
    (sigma : Q →* T) (N : Subgroup (MFCamouflage.Camouflage d Q)) :
    (∀ x ∈ N, (sigma.comp (MFCamouflage.projection d Q)) x = 1) ↔
      ∀ y ∈ N.map (MFCamouflage.projection d Q), sigma y = 1 := by
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  · intro h x hx
    exact h _ ⟨x, hx, rfl⟩

/-- **Sentence 293.**  A quotient of the camouflage group is MF exactly when
the relation subgroup contains the hidden kernel and the visible quotient is
MF. -/
theorem manuscriptSentence293_quotient_MF_iff
    [Countable B] [Countable Q]
    (d : B) (hfull : actualCoronaMFResidual B = ⊤)
    (N : Subgroup (MFCamouflage.Camouflage d Q)) [N.Normal] :
    IsCDEOperatorMF (MFCamouflage.Camouflage d Q ⧸ N) ↔
      (MFCamouflage.projection d Q).ker ≤ N ∧
        IsCDEOperatorMF
          (Q ⧸ N.map (MFCamouflage.projection d Q)) :=
  MFCamouflage.quotient_isCDEOperatorMF_iff d Q hfull N

/-- **Sentence 294.**  Once the projection kernel lies in `N`, the relation
subgroup is recovered from its visible image. -/
theorem manuscriptSentence294_preimageOfImage
    (d : B) (N : Subgroup (MFCamouflage.Camouflage d Q))
    (hker : (MFCamouflage.projection d Q).ker ≤ N) :
    (N.map (MFCamouflage.projection d Q)).comap
        (MFCamouflage.projection d Q) = N :=
  Subgroup.comap_map_eq_self hker

end OneSidedMFRadical
end Manuscript
end GroupApproximation
