import GroupApproximation.Manuscript.NonMFSentences.IntroSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Algebra.CountableInstances
import GroupApproximation.Meta.AxiomGuard

/-!
# Corona homomorphisms: images, kernels, and the largest MF quotient

`non_mf_groups_exist.tex`, subsection "Corona homomorphisms".

Proof of Lemma `prop:mf-residual-calculus`, lines 377--379:

> The image of a corona homomorphism is a countable MF group.  Conversely,
> compose a homomorphism to an MF group with a corona embedding of its image;
> the resulting corona homomorphism has the same kernel.

Lines 384--386:

> For countable $G$ the quotient
> $G/\operatorname{Rad}_{\mathrm{MF}}(G)$ is again MF, and hence the largest
> MF quotient of $G$: ...

In the corpus, "MF" is `IsCDEOperatorMF` (a faithful unitary representation
in a norm matrix corona with natural dimensions `d n`, `d` strictly
increasing), and `Rad_MF(G)` is `manuscriptCoronaMFResidual G`.

Proof route.
* Image. A corona homomorphism `Theta : G →* U(∏ M_{X n} / ⊕ M_{X n})` has a
  countable image `Theta.range`, since it is the surjective image of `G`
  (`coronaImage_countable`). The inclusion of the image is a faithful corona
  representation, which gives both `IsCDEOperatorMF` and `IsOperatorMF`.
* Same kernel. An MF target `M` has a faithful corona representation `rho`.
  Restricting `rho` to `f(G) ≤ M` gives a corona embedding `iota` of the
  image. The image is countable and MF. The kernel of `iota ∘ f` is `ker f`,
  because `iota` is injective.
* Largest MF quotient.
  * The quotient is MF by `manuscriptCoronaMFQuotient_isCDEOperatorMF`.
  * If `G/N` is MF, the quotient map is a homomorphism to an MF group, so it
    kills `Rad_MF(G)` by the printed radical formula
    `manuscriptSentence_mfRadicalFormula`. Hence `Rad_MF(G) ≤ N`.
  * Every homomorphism to an MF group kills the radical, so it factors
    uniquely through the quotient.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditCompress1

open GroupApproximation.Manuscript.OneSidedMFRadical
open GroupApproximation.Manuscript.NonMFSentences (manuscriptSentence_mfRadicalFormula)

attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- tex 377: the image of a corona homomorphism is a countable MF group. -/
theorem manuscriptSentence_coronaImageIsCountableMFGroup (G : Type) [Group G]
    [Countable G] (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Theta : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    ∃ _ : Countable Theta.range,
      IsCDEOperatorMF Theta.range ∧ IsOperatorMF Theta.range := by
  letI hcount : Countable Theta.range := coronaImage_countable G X Theta
  have hX : ∀ n, 0 < Fintype.card (X n) := fun _ ↦ Fintype.card_pos
  exact ⟨hcount,
    isCDEOperatorMF_of_coronaEmbedding Theta.range X hX Theta.range.subtype
      Theta.range.subtype_injective,
    coronaImage_isOperatorMF G X hX Theta⟩

#audit_axioms manuscriptSentence_coronaImageIsCountableMFGroup

/-- tex 377--379: for a homomorphism `f` from `G` to an MF group `M`, the image
`f(G)` is a countable MF group with a corona embedding `iota`. The corona
homomorphism `iota ∘ f` has the same kernel as `f`. -/
theorem manuscriptSentence_composeWithImageEmbeddingSameKernel (G M : Type)
    [Group G] [Group M] [Countable M] (hM : IsCDEOperatorMF M) (f : G →* M) :
    ∃ _ : Countable f.range, IsCDEOperatorMF f.range ∧
      ∃ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
          Fintype.card_pos_iff.mp (by simpa using hd n)
        ∃ iota : f.range →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          Function.Injective iota ∧ (iota.comp f.rangeRestrict).ker = f.ker := by
  obtain ⟨d, hd, -, rho, hrho⟩ := hM
  letI hcount : Countable f.range := Subtype.countable
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) := fun n ↦
    Fintype.card_pos_iff.mp (by simpa using hd n)
  have hX : ∀ n, 0 < Fintype.card (naturalFiniteModel (d n)) := fun _ ↦
    Fintype.card_pos
  have hinj : Function.Injective (rho.comp f.range.subtype) :=
    hrho.comp f.range.subtype_injective
  refine ⟨hcount,
    isCDEOperatorMF_of_coronaEmbedding f.range (fun n ↦ naturalFiniteModel (d n))
      hX (rho.comp f.range.subtype) hinj,
    d, hd, rho.comp f.range.subtype, hinj, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    have h1 : f.rangeRestrict g = 1 :=
      hinj (h.trans (map_one (rho.comp f.range.subtype)).symm)
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.coe_rangeRestrict] at h2
    exact h2
  · intro h
    have h1 : f.rangeRestrict g = 1 :=
      Subtype.ext (by rw [MonoidHom.coe_rangeRestrict]; exact h)
    rw [h1, map_one]

#audit_axioms manuscriptSentence_composeWithImageEmbeddingSameKernel

/-- tex 384--386: for countable `G`, the quotient `G / Rad_MF(G)` is MF, and it
is the largest MF quotient of `G`:
* every normal `N` with `G/N` MF contains `Rad_MF(G)`;
* every homomorphism from `G` to a countable MF group factors uniquely
  through `G / Rad_MF(G)`. -/
theorem manuscriptSentence_mfRadicalQuotientLargestMFQuotient (G : Type)
    [Group G] [Countable G] :
    IsCDEOperatorMF (G ⧸ manuscriptCoronaMFResidual G) ∧
      (∀ (N : Subgroup G) [N.Normal], IsCDEOperatorMF (G ⧸ N) →
        manuscriptCoronaMFResidual G ≤ N) ∧
      (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        ∀ f : G →* M, ∃! fBar : G ⧸ manuscriptCoronaMFResidual G →* M,
          fBar.comp (QuotientGroup.mk' (manuscriptCoronaMFResidual G)) = f) := by
  refine ⟨manuscriptCoronaMFQuotient_isCDEOperatorMF, ?_, ?_⟩
  · intro N _ hN x hx
    have h : QuotientGroup.mk' N x = 1 :=
      (manuscriptSentence_mfRadicalFormula G x).mp hx (G ⧸ N) hN
        (QuotientGroup.mk' N)
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff (N := N) x).mp h
  · intro M _ _ hM f
    have hle : manuscriptCoronaMFResidual G ≤ f.ker := by
      intro x hx
      exact MonoidHom.mem_ker.mpr
        ((manuscriptSentence_mfRadicalFormula G x).mp hx M hM f)
    refine ⟨QuotientGroup.lift (manuscriptCoronaMFResidual G) f hle,
      QuotientGroup.lift_comp_mk' (manuscriptCoronaMFResidual G) f hle, ?_⟩
    intro g hg
    apply QuotientGroup.monoidHom_ext
    rw [hg, QuotientGroup.lift_comp_mk']

#audit_axioms manuscriptSentence_mfRadicalQuotientLargestMFQuotient

end GroupApproximation.Manuscript.NonMF.AuditCompress1
