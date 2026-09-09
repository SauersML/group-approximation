import GroupApproximation.Analysis.FiniteDimensionalCStarMatrixCPRetract
import GroupApproximation.Analysis.LanceAmenableOverlap
import GroupApproximation.Analysis.LanceNFUnitalCPAP
import GroupApproximation.Meta.AxiomGuard

/-!
# The corpus-wide approximation property implies the translation-tested one

## What was missing, and what is here

`Manuscript/OneSidedMFRadical/ReducedCStarNotNuclear.lean` carries an explicit
leading binder `TranslationCPAPReductionInput`:

> `∀ (Γ : Type) [Group Γ], IsNuclearCStarAlgebra (ReducedGroupCStar Γ) →
>   NuclearReducedCPAP Γ`

and its docstring, together with the "Lance, discharged" section of
`metadata/LITERATURE_QUARANTINE.md`, records the two facts that reduction was
said to hide:

1. **The finite-dimensional target must be a block.**  `IsNuclearMap` factors
   the identity through an arbitrary `FinDimCStarAlgebra`, while the Arveson
   extension consumed downstream extends maps into a matrix algebra and
   nothing else.  Bridging is injectivity of a finite-dimensional
   C⋆-algebra — Wedderburn plus a completely positive retraction.
2. **Contractive is not unital.**  `IsNuclearMap` asks its maps only for
   `‖α a‖ ≤ ‖a‖`, while `NuclearReducedCPAP` asks for `α 1 = 1`.

**Both are now theorems of this repository**, landed by other lanes after that
record was written, and this module is the observation that the reduction is
therefore no longer missing:

* fact 1 is `BlackadarKirchberg.exists_matrix_ucp_retraction_of_finiteDimensionalCStar`
  (a nontrivial finite-dimensional complex C⋆-algebra carries a unital
  ⋆-embedding into a full matrix algebra together with a unital, completely
  positive, contractive retraction);
* fact 2 is `additiveUnitalization` of `Analysis/LanceCPContractiveUnitalization`
  with its quantitative estimate `norm_additiveUnitalization_comp_sub_le_four_mul`
  — the repair is additive, `φ + ω(·)(1 - φ 1)`, rather than the conjugation by
  `(φ 1 + δ)^{-1/2}` the record anticipated, and it costs a factor four.

## The two steps

`exists_matrixModelApproximation_of_isNuclearCStarAlgebra` runs the retract of
fact 1 through a nuclear approximation.  Embedding after the downward map and
retracting before the upward one changes neither complete positivity nor
contractivity, and leaves the composite **pointwise unchanged**, because
`retract ∘ embedding = id` exactly; so the recovery estimate is carried across
with no loss.  The degenerate case — a nuclear approximation through the zero
algebra — is not excluded by hypothesis and is handled by the zero maps
through a one-by-one block, which recover exactly what the degenerate
approximation recovered.

`nuclearReducedCPAP_of_isNuclearCStarAlgebra` is then the argument of
`nuclearReducedCPAP_of_isNFAlgebra`, verbatim except that the matrix models
come from the previous step instead of from an NF hypothesis: test on the
translations together with the unit, at tolerance `ε / 4`, additively
unitalize both legs, and transport the matrix block to `B(ℂᵏ)` along the
canonical ⋆-equivalence.  The approximately multiplicative clause of an NF
approximation was never used there, which is why the same proof runs from
nuclearity alone.

## What this does not say

It does not identify the repository's nuclearity predicates with one another.
`CStarTensor.IsNuclearCStar` (`min = max`) is untouched, and no equivalence
with either approximation property is claimed.  What is proved is one
implication between the two approximation properties, in the direction the
Lance route consumes.

## Manuscript status

Discharges `TranslationCPAPReductionInput`; with
`LanceAmenableOverlap.nuclearReducedCPAP_iff_isAmenable` this gives Lance's
theorem in the hard direction at the corpus-wide definition, for every
discrete group and with no hypothesis.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace Matrix.Norms.L2Operator
open ReducedGroupCStarTrace

universe u

noncomputable section

local instance matrixBlockCStarAlgebraForLanceForward
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-! ## The zero map is completely positive

Needed only for the degenerate branch below: nothing in `IsNuclearMap`
forbids the approximating algebra from being the zero algebra, and the zero
maps through a one-by-one block reproduce exactly the same composite. -/

/-- The zero linear map between C⋆-algebras is completely positive. -/
theorem isCompletelyPositive_zero {A : Type*} {B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    IsCompletelyPositive (0 : A →ₗ[ℂ] B) := by
  intro n M _
  refine ⟨0, ?_⟩
  have hzero : (star (0 : CStarMatrix (Fin n) (Fin n) B) * 0) = 0 := by
    simp
  rw [hzero]
  ext i j
  rfl

/-! ## Step one: a matrix model for a nuclear approximation -/

/-- **Nuclearity gives matrix models.**  A C⋆-algebra with the completely
positive approximation property admits, on every finite set and at every
tolerance, completely positive contractions through a *full matrix algebra*
whose composite recovers the set.

The approximating algebra supplied by `IsNuclearMap` is an arbitrary
finite-dimensional C⋆-algebra.  It is a unital completely positive contractive
retract of a matrix algebra, and inserting the embedding and the retraction
leaves the composite pointwise unchanged, so the recovery estimate transfers
with no loss at all. -/
theorem exists_matrixModelApproximation_of_isNuclearCStarAlgebra
    {A : Type u} [CStarAlgebra A] (h : IsNuclearCStarAlgebra A)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (hY : Nonempty Y),
      letI : Nonempty Y := hY
      ∃ (down : A →ₗ[ℂ] Matrix Y Y ℂ) (up : Matrix Y Y ℂ →ₗ[ℂ] A),
        IsCompletelyPositive down ∧
          IsCompletelyPositive up ∧
          (∀ a : A, ‖down a‖ ≤ ‖a‖) ∧
          (∀ d : Matrix Y Y ℂ, ‖up d‖ ≤ ‖d‖) ∧
          ∀ a ∈ F, ‖up (down a) - a‖ ≤ ε := by
  classical
  obtain ⟨D, alpha, beta, halpha, hbeta, halphaContract, hbetaContract,
    happrox⟩ := h F ε hε
  rcases subsingleton_or_nontrivial ↥D with hD | hD
  · -- the approximating algebra is the zero algebra: both maps are zero
    haveI : Subsingleton ↥D := hD
    refine ⟨⟨Fin 1, inferInstance, inferInstance⟩, ⟨0⟩, 0, 0,
      isCompletelyPositive_zero, isCompletelyPositive_zero, ?_, ?_, ?_⟩
    · intro a
      simp
    · intro d
      simp
    · intro a ha
      have hval : beta (alpha a) = 0 := by
        have hz : alpha a = 0 := Subsingleton.elim _ _
        rw [hz, map_zero]
      have hap := happrox a ha
      rw [hval] at hap
      simpa using hap
  · haveI : Nontrivial ↥D := hD
    obtain ⟨Y, hYf, hYd, hYn, emb, ret, hretCP, -, hretEmb, hretNorm⟩ :=
      BlackadarKirchberg.exists_matrix_ucp_retraction_of_finiteDimensionalCStar
        ↥D
    letI : Fintype Y := hYf
    letI : DecidableEq Y := hYd
    letI : Nonempty Y := hYn
    refine ⟨⟨Y, hYf, hYd⟩, hYn,
      (emb : ↥D →ₗ[ℂ] Matrix Y Y ℂ).comp alpha, beta.comp ret,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact (isCompletelyPositive_of_starAlgHom
        emb.toNonUnitalStarAlgHom).comp halpha
    · exact hbeta.comp hretCP
    · intro a
      calc ‖emb (alpha a)‖
          ≤ ‖alpha a‖ := NonUnitalStarAlgHom.norm_apply_le emb (alpha a)
        _ ≤ ‖a‖ := halphaContract a
    · intro d
      calc ‖beta (ret d)‖ ≤ ‖ret d‖ := hbetaContract _
        _ ≤ ‖d‖ := hretNorm d
    · intro a ha
      have hval : beta (ret (emb (alpha a))) = beta (alpha a) := by
        rw [hretEmb]
      show ‖beta (ret (emb (alpha a))) - a‖ ≤ ε
      rw [hval]
      exact happrox a ha

/-! ## Step two: the translation-tested, unital, matrix form -/

/-- **The reduction, for every discrete group.**  The completely positive
approximation property of `C⋆_λ(G)` — the identity map is point-norm
approximable by completely positive contractions through finite-dimensional
C⋆-algebras — implies the translation-tested unital form
`NuclearReducedCPAP` that the Lance route consumes.

This is the argument of `nuclearReducedCPAP_of_isNFAlgebra`, whose NF
hypothesis was only ever used for its completely positive contractions: the
matrix models are supplied here by
`exists_matrixModelApproximation_of_isNuclearCStarAlgebra` instead. -/
theorem nuclearReducedCPAP_of_isNuclearCStarAlgebra
    (G : Type) [Group G]
    (hnuc : IsNuclearCStarAlgebra (ReducedGroupCStar G)) :
    NuclearReducedCPAP G := by
  classical
  intro F epsilon hepsilon
  let translation : G → ReducedGroupCStar G := fun g ↦
    ⟨leftRegularOperator G g, mem_reduced_leftRegularOperator g⟩
  let S : Finset (ReducedGroupCStar G) :=
    insert 1 (F.image translation)
  have hquarter : 0 < epsilon / 4 := div_pos hepsilon (by norm_num)
  obtain ⟨Y, hY, down, up, hdownCP, hupCP, hdownContract,
      hupContract, hrecover⟩ :=
    exists_matrixModelApproximation_of_isNuclearCStarAlgebra hnuc S
      (epsilon / 4) hquarter
  letI : Nonempty Y := hY
  let omegaA : CStarState.State (ReducedGroupCStar G) :=
    (CStarState.State.exists_star_mul_self (1 : ReducedGroupCStar G)).choose
  let omegaY : CStarState.State (Matrix Y Y ℂ) :=
    (CStarState.State.exists_star_mul_self (1 : Matrix Y Y ℂ)).choose
  let downU := additiveUnitalization down omegaA
  let upU := additiveUnitalization up omegaY
  have hdownU : IsCompletelyPositive downU ∧ downU 1 = 1 :=
    additiveUnitalization_completelyPositive_unital
      down omegaA hdownCP hdownContract
  have hupU : IsCompletelyPositive upU ∧ upU 1 = 1 :=
    additiveUnitalization_completelyPositive_unital
      up omegaY hupCP hupContract
  have hrecoverOne : ‖up (down 1) - 1‖ ≤ epsilon / 4 :=
    hrecover 1 (Finset.mem_insert_self 1 _)
  let e := finiteModelOperatorStarAlgEquiv Y
  let downOp :=
    (BlackadarKirchberg.starAlgEquivLinearMap e).comp downU
  let upReduced :=
    upU.comp (BlackadarKirchberg.starAlgEquivLinearMap e.symm)
  let inclStar :=
    (reducedGroupCStarSubalgebra G).subtype.toNonUnitalStarAlgHom
  let incl : ↥(reducedGroupCStarSubalgebra G) →ₗ[ℂ]
      (GroupHilbert G →L[ℂ] GroupHilbert G) := inclStar
  let upOp := incl.comp upReduced
  have heCP : IsCompletelyPositive
      (BlackadarKirchberg.starAlgEquivLinearMap e) :=
    isCompletelyPositive_of_starAlgHom
      e.toStarAlgHom.toNonUnitalStarAlgHom
  have heSymmCP : IsCompletelyPositive
      (BlackadarKirchberg.starAlgEquivLinearMap e.symm) :=
    isCompletelyPositive_of_starAlgHom
      e.symm.toStarAlgHom.toNonUnitalStarAlgHom
  have hinclCP : IsCompletelyPositive incl := by
    dsimp only [incl]
    exact isCompletelyPositive_of_starAlgHom inclStar
  have hdownOpCP : IsCompletelyPositive downOp := heCP.comp hdownU.1
  have hupReducedCP : IsCompletelyPositive upReduced := hupU.1.comp heSymmCP
  have hupOpCP : IsCompletelyPositive upOp := hinclCP.comp hupReducedCP
  refine ⟨Fintype.card Y, downOp, upOp, ?_, ?_, ?_, hupOpCP, ?_, ?_, ?_⟩
  · intro m a v
    by_cases hm : m = 0
    · subst m
      simp
    · letI : NeZero m := ⟨hm⟩
      exact (hdownOpCP.form_nonneg a v).1
  · intro a
    exact OrderZero.map_star_of_cp hdownOpCP a
  · dsimp only [downOp, LinearMap.comp_apply]
    rw [hdownU.2]
    exact map_one e
  · dsimp only [upOp, upReduced, incl, LinearMap.comp_apply]
    rw [BlackadarKirchberg.starAlgEquivLinearMap_apply, map_one e.symm, hupU.2]
    rfl
  · intro T
    dsimp only [upOp, incl, LinearMap.comp_apply]
    exact (upReduced T).property
  · intro g hg
    have htranslationMem : translation g ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    have hrepair :
        ‖upU (downU (translation g)) - translation g‖ ≤ epsilon := by
      have h := norm_additiveUnitalization_comp_sub_le_four_mul
        down up omegaA omegaY hdownCP hupCP hdownContract hupContract
        hrecoverOne (translation g)
        (by
          change ‖leftRegularOperator G g‖ ≤ 1
          exact norm_leftRegularOperator_le_one G g)
        (hrecover _ htranslationMem)
      change ‖upU (downU (translation g)) - translation g‖ ≤ epsilon
      have hfour : 4 * (epsilon / 4) = epsilon := by ring
      rw [← hfour]
      exact h
    change ‖upOp (downOp (translation g)) - leftRegularOperator G g‖ ≤ epsilon
    have hval : upOp (downOp (translation g)) =
        (upU (downU (translation g)) : ReducedGroupCStar G) := by
      simp only [upOp, upReduced, downOp, incl, LinearMap.comp_apply,
        BlackadarKirchberg.starAlgEquivLinearMap_apply,
        StarAlgEquiv.symm_apply_apply]
      rfl
    rw [hval]
    exact hrepair

/-! ## Lance's theorem, hard direction, at the corpus-wide definition -/

/-- **Nuclear implies amenable, for every discrete group.**  If the reduced
C⋆-algebra of a discrete group has the completely positive approximation
property of `Analysis/CStarExactness`, the group is amenable.

This is the direction the manuscript's nonnuclearity paragraph appeals to.  It
is now a theorem here, with no hypothesis: the reduction above lands in
`NuclearReducedCPAP`, and `nuclearReducedCPAP_iff_isAmenable` closes the gap
to amenability. -/
theorem isAmenable_of_isNuclearCStarAlgebra_reducedGroupCStar
    (G : Type) [Group G]
    (hnuc : IsNuclearCStarAlgebra (ReducedGroupCStar G)) :
    Amenability.IsAmenable G :=
  nuclearReducedCPAP_iff_isAmenable.mp
    (nuclearReducedCPAP_of_isNuclearCStarAlgebra G hnuc)

/-- The contrapositive, in the form every non-nuclearity endpoint uses: a
nonamenable discrete group has a non-nuclear reduced C⋆-algebra. -/
theorem not_isNuclearCStarAlgebra_reducedGroupCStar_of_not_isAmenable
    (G : Type) [Group G] (hG : ¬ Amenability.IsAmenable G) :
    ¬ IsNuclearCStarAlgebra (ReducedGroupCStar G) :=
  fun hnuc ↦ hG (isAmenable_of_isNuclearCStarAlgebra_reducedGroupCStar G hnuc)

end

end CStarExactness
end GroupApproximation

open GroupApproximation.CStarExactness

-- These take the nuclearity of a named algebra as an ordinary mathematical
-- hypothesis, so the closed-endpoint gate would reject them by design; the
-- axiom closure is still pinned.
#audit_axioms
  GroupApproximation.CStarExactness.nuclearReducedCPAP_of_isNuclearCStarAlgebra

#audit_axioms
  GroupApproximation.CStarExactness.isAmenable_of_isNuclearCStarAlgebra_reducedGroupCStar
