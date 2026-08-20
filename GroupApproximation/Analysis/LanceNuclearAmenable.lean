import GroupApproximation.Analysis.LanceAmenableOverlap
import GroupApproximation.Analysis.LanceMatrixSubalgebra
import GroupApproximation.Analysis.NuclearApproximationEstimate
import GroupApproximation.Analysis.TikuisisWhiteWinter

/-!
# Lance's theorem: the reduced algebra of an amenable group is nuclear

This closes the forward half of the Lance debt at the definition
`CStarExactness.IsNuclearCStarAlgebra` --- the completely positive
approximation property of `Analysis/CStarExactness`, which is what
`QuasidiagonalMF.AmenableNuclearInput` asks for --- rather than at the
group-flavoured `NuclearReducedCPAP` of `Analysis/LanceNuclearity`.

The two differ in exactly one place.  `NuclearReducedCPAP` tests the
approximation on **translations**; `IsNuclearMap` tests it on an arbitrary
finite set of **algebra elements**, requires both maps to be contractions, and
wants the factorization to run through a bundled finite-dimensional
C⋆-algebra.  Bridging is the standard `ε/3`:

* every element of `C⋆_λ(G)` is within `ε/3` of a finite combination of
  translations (`ReducedGroupCStarTrace.exists_translationSum_approx`, which
  is where the collapse `adjoin = span` is used);
* on that combination the factorization acts diagonally, by the overlaps
  (`folnerUp_compression_leftRegular`), so the error is the coefficient mass
  times the overlap defect --- choose the Følner tolerance to be `ε/3` over
  the mass;
* both maps are unital and completely positive, hence contractions
  (`IsCompletelyPositive.norm_apply_le_of_unital`), so the outer two thirds
  are controlled by the first bullet.

Complete positivity of the *corestricted* Følner map --- the one landing in
the subalgebra rather than in `B(ℓ²(G))` --- is
`LanceMatrixSubalgebra.exists_entries_mem_factor`: positivity permanence
with a factorization whose entries stay in the subalgebra.  The bundled
target is `NuclearApproximationEstimate.finDimOperatorBlock`.

## The two nuclearity predicates, and which direction is proved

`isNuclearCStarAlgebra_of_nuclearReducedCPAP` records that the CPAP of
`Analysis/LanceNuclearity` implies the corpus-wide `IsNuclearCStarAlgebra`.
The route is not a transport of the CPAP's own maps: `LanceNuclearity` turns
the CPAP into an invariant mean, and this file turns an invariant mean back
into a factorization, so the two notions meet **through amenability** --- which
is the shape Lance's theorem has.

The converse is **not** proved, is not claimed, and --- deliberately --- is not
even *stated* with its gap as a hypothesis.  Writing it as
`IsNuclearCStarAlgebra (C⋆_λ Γ) ↔ IsAmenable Γ` under a `blockForm` premise
would be the first shape `scripts/check_non_mf_unconditional.py` misreads: that
gate takes the **left** side of an `↔` as the conclusion and judges a premise
that is a bare logical formula by the head symbols it mentions, so such a
declaration reads as a premise-free producer and would take
`IsNuclearCStarAlgebra` off `--audit-corpus`.  Two implications would avoid the
`↔` trap and still hit the bare-premise one.  So the missing reduction is
recorded here, in prose, and nowhere in a type.

The reduction is `IsNuclearCStarAlgebra (C⋆_λ H) → NuclearReducedCPAP H`, and
what it hides is two facts, neither of them about groups.  Both were found by
reading what `LanceCPApprox.hasInvariantMean_of_cpApprox` actually consumes ---
a **unital** completely positive map defined on all of `B(ℓ²(G))` with values
in `L(G)`:

1. **The finite-dimensional target has to be a block.**  `IsNuclearMap` factors
   the identity through an arbitrary `FinDimCStarAlgebra`, and the Arveson
   extension this development proves (`Analysis/LanceMatrixArveson`) extends a
   map into `B(ℂᵏ)` and nothing else.  Getting from one to the other is
   injectivity of a finite-dimensional C⋆-algebra: a unital embedding into some
   `B(ℂᵏ)` together with a completely positive retraction onto its image.  That
   is Wedderburn plus the conditional expectation, and neither is formalized.
2. **Contractive is not unital.**  `IsNuclearMap` asks its two maps only for
   `‖α a‖ ≤ ‖a‖`; `NuclearReducedCPAP`, and the Arveson step under it, ask for
   `α 1 = 1`.  The repair is the standard one --- conjugate by
   `(α 1 + δ)^{-1/2}` and absorb the defect into the tolerance --- and it is
   real work with the continuous functional calculus, not bookkeeping.  It is
   easy to miss because every *construction* in this lane produces unital maps
   and only the *definition* forgets.

So `Analysis/LanceNuclearity.reducedGroupCStar_not_nuclear` remains the
statement about `NuclearReducedCPAP` rather than about
`IsNuclearCStarAlgebra`: substituting the latter there would weaken it by
exactly the two facts above.

## Manuscript status

Discharges `QuasidiagonalMF.AmenableNuclearInput` --- the Lance row of
`metadata/LITERATURE_QUARANTINE.md` --- outright.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset ReducedGroupCStarTrace Amenability

noncomputable section

universe u

variable {G : Type u} [Group G]

/-! ## The factorization acts diagonally on combinations of translations -/

/-- On a finite combination of translations the Følner factorization acts by
the overlaps, so the error is the coefficient mass times the defect. -/
theorem norm_folner_sub_le {k n : ℕ} (e : Fin k → G) (c : Fin k → ℂ)
    (cc : Fin n → ℂ) (γ : Fin n → G) {δ : ℝ}
    (hov : ∀ i, ‖folnerOverlap e c (γ i) - 1‖ ≤ δ) :
    ‖folnerUp e c (compressionLM (folnerIncl e)
        (∑ i : Fin n, cc i • leftRegularOperator G (γ i)))
      - ∑ i : Fin n, cc i • leftRegularOperator G (γ i)‖
      ≤ (∑ i : Fin n, ‖cc i‖) * δ := by
  have hlin : folnerUp e c (compressionLM (folnerIncl e)
        (∑ i : Fin n, cc i • leftRegularOperator G (γ i)))
      = ∑ i : Fin n,
          cc i • (folnerOverlap e c (γ i) • leftRegularOperator G (γ i)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, folnerUp_compression_leftRegular]
  rw [hlin, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ ↦ ?_)
  have hterm : cc i • (folnerOverlap e c (γ i) • leftRegularOperator G (γ i))
      - cc i • leftRegularOperator G (γ i)
      = (cc i * (folnerOverlap e c (γ i) - 1))
          • leftRegularOperator G (γ i) := by
    rw [smul_smul, mul_sub, mul_one, sub_smul]
  rw [hterm]
  -- `norm_smul_le` is stated at the seminormed-group norm and the operator
  -- norm reaches it by a different path, so the equation is used instead
  have hsm : ‖(cc i * (folnerOverlap e c (γ i) - 1))
        • leftRegularOperator G (γ i)‖
      = ‖cc i * (folnerOverlap e c (γ i) - 1)‖
        * ‖leftRegularOperator G (γ i)‖ := norm_smul _ _
  rw [hsm, norm_mul]
  calc ‖cc i‖ * ‖folnerOverlap e c (γ i) - 1‖
        * ‖leftRegularOperator G (γ i)‖
      ≤ ‖cc i‖ * δ * 1 := by
        -- `gcongr` opens a nonnegativity side goal first; the two bounds are
        -- the overlap estimate and the unitarity of the left regular operator
        gcongr
        · exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hov i))
        · exact hov i
        · exact norm_leftRegularOperator_le_one G (γ i)
    _ = ‖cc i‖ * δ := mul_one _

/-- A single left translation is fixed up to its scalar Følner-overlap defect. -/
theorem norm_folner_compression_sub_leftRegular_le {k : ℕ}
    (e : Fin k → G) (c : Fin k → ℂ) (g : G) {δ : ℝ}
    (hov : ‖folnerOverlap e c g - 1‖ ≤ δ) :
    ‖folnerUp e c (compressionLM (folnerIncl e) (leftRegularOperator G g))
        - leftRegularOperator G g‖ ≤ δ := by
  rw [folnerUp_compression_leftRegular]
  calc
    ‖folnerOverlap e c g • leftRegularOperator G g - leftRegularOperator G g‖ =
        ‖(folnerOverlap e c g - 1) • leftRegularOperator G g‖ := by
          rw [sub_smul, one_smul]
    _ = ‖folnerOverlap e c g - 1‖ * ‖leftRegularOperator G g‖ := norm_smul _ _
    _ ≤ δ * 1 := by
      gcongr
      · exact (norm_nonneg _).trans hov
      · exact norm_leftRegularOperator_le_one G g
    _ = δ := mul_one _

/-! ## The corestricted Følner map -/

/-- The Følner map, corestricted to the reduced algebra. -/
def folnerUpCore {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ) :
    (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ]
      ReducedGroupCStar G where
  toFun T := ⟨folnerUp e c T, folnerUp_mem_reduced e c T⟩
  map_add' S T := by
    refine Subtype.ext ?_
    show folnerUp e c (S + T) = folnerUp e c S + folnerUp e c T
    rw [map_add]
  map_smul' r T := by
    refine Subtype.ext ?_
    show folnerUp e c (r • T) = r • folnerUp e c T
    rw [map_smul]

@[simp] theorem folnerUpCore_coe {k : ℕ} (e : Fin k → G) (c : Fin k → ℂ)
    (T : EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :
    ((folnerUpCore e c T : ReducedGroupCStar G) :
      GroupHilbert G →L[ℂ] GroupHilbert G) = folnerUp e c T :=
  rfl

/-- **The corestricted Følner map is completely positive.**  Positivity
permanence for the closed subalgebra supplies a factorization whose entries
stay inside it. -/
theorem isCompletelyPositive_folnerUpCore {k : ℕ} (e : Fin k → G)
    (c : Fin k → ℂ) :
    IsCompletelyPositive (folnerUpCore e c) := by
  classical
  intro n Y hY
  have hpos : (0 : CStarMatrix (Fin n) (Fin n)
      (GroupHilbert G →L[ℂ] GroupHilbert G)) ≤ Y.map ⇑(folnerUp e c) :=
    map_nonneg_of_isCompletelyPositive (isCompletelyPositive_folnerUp e c) n Y
      (by obtain ⟨N, hN⟩ := hY; rw [hN]; exact star_mul_self_nonneg N)
  obtain ⟨N, hmemN, hfac⟩ :=
    exists_entries_mem_factor (reducedGroupCStarSubalgebra G)
      (isClosed_reducedGroupCStar G)
      (fun p q ↦ folnerUp_mem_reduced e c (Y p q)) hpos
  let F : CStarMatrix (Fin n) (Fin n) (ReducedGroupCStar G) :=
    fun p q ↦ (⟨N p q, hmemN p q⟩ : ReducedGroupCStar G)
  refine ⟨F, ?_⟩
  apply CStarMatrix.ext
  intro i j
  refine Subtype.ext ?_
  -- the left side is a coercion of a corestriction, so it is the ambient
  -- entry on the nose
  have hL : ((Y.map ⇑(folnerUpCore e c)) i j :
      GroupHilbert G →L[ℂ] GroupHilbert G) = (Y.map ⇑(folnerUp e c)) i j := rfl
  -- the right side is the only place a matrix product over the subalgebra has
  -- to be compared with one over the ambient algebra: expand both by
  -- `Matrix.mul_apply`, pull the coercion through the sum, and the summands
  -- agree definitionally because subtype `*` and `star` are the ambient ones
  have hR : (((star F * F) i j : ReducedGroupCStar G) :
      GroupHilbert G →L[ℂ] GroupHilbert G)
      = (star N * N) i j := by
    -- both entries are sums over the middle index, and the summands agree
    -- because the subtype's `*` and `star` are the ambient ones
    have hsub : ((star F * F) i j : ReducedGroupCStar G)
        = ∑ r, star (F r i) * F r j := by
      rw [cstarMatrix_mul_apply]
      exact Finset.sum_congr rfl fun r _ ↦ by rw [cstarMatrix_star_apply]
    have hamb : (star N * N) i j = ∑ r, star (N r i) * N r j := by
      rw [cstarMatrix_mul_apply]
      exact Finset.sum_congr rfl fun r _ ↦ by rw [cstarMatrix_star_apply]
    calc
      (((star F * F) i j : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G)
          = ((∑ r, star (F r i) * F r j : ReducedGroupCStar G) :
              GroupHilbert G →L[ℂ] GroupHilbert G) :=
            congrArg (fun z : ReducedGroupCStar G ↦
              (z : GroupHilbert G →L[ℂ] GroupHilbert G)) hsub
      _ = ∑ r, star (N r i) * N r j := by
            push_cast
            exact Finset.sum_congr rfl fun r _ ↦ rfl
      _ = (star N * N) i j := hamb.symm
  calc
    ((Y.map ⇑(folnerUpCore e c)) i j : ReducedGroupCStar G) =
        (Y.map ⇑(folnerUp e c)) i j := hL
    _ = (star N * N) i j := congrFun (congrFun hfac i) j
    _ = (((star F * F) i j : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G) := hR.symm

/-! ## Nuclearity -/

-- Dependent choices `Nn`, `CC`, and `GG` keep the finite-set witness compact,
-- but normalizing their indexed sums needs slightly more than Lean's default
-- heartbeat budget.  Keep the allowance on this construction alone.
set_option maxHeartbeats 400000 in
/-- **Lance's theorem, forward direction, at the CPAP definition.**

The `k` the overlap producer hands out carries no positivity clause and needs
none: `NuclearApproximationEstimate.finDimOperatorBlock` is a C⋆-algebra for
every `k`, including `0`. -/
theorem isNuclearCStarAlgebra_of_overlap
    (h : ∀ (F : Finset G) (δ : ℝ), 0 < δ →
      ∃ (k : ℕ) (e : Fin k → G) (c : Fin k → ℂ),
        Function.Injective e ∧ (∑ p : Fin k, star (c p) * c p) = 1 ∧
          ∀ g ∈ F, ‖folnerOverlap e c g - 1‖ ≤ δ) :
    IsNuclearCStarAlgebra (ReducedGroupCStar G) := by
  classical
  show IsNuclearMap
    (LinearMap.id : ReducedGroupCStar G →ₗ[ℂ] ReducedGroupCStar G)
  refine isNuclearMap_of_operatorBlock ?_
  intro S ε hε
  have hall : ∀ x : ReducedGroupCStar G,
      ∃ (m : ℕ) (cc : Fin m → ℂ) (γ : Fin m → G),
        ‖(x : GroupHilbert G →L[ℂ] GroupHilbert G)
          - ∑ i : Fin m, cc i • leftRegularOperator G (γ i)‖ < ε / 3 :=
    fun x ↦ exists_translationSum_approx G x.2 (div_pos hε (by norm_num))
  choose Nn CC GG happrox using hall
  set Sset : Finset G :=
    S.biUnion (fun x ↦ Finset.image (GG x) Finset.univ) with hSset
  set Mb : ℝ := 1 + ∑ x ∈ S, ∑ i : Fin (Nn x), ‖CC x i‖ with hMb
  have hMpos : 0 < Mb := by
    have hnn : (0 : ℝ) ≤ ∑ x ∈ S, ∑ i : Fin (Nn x), ‖CC x i‖ :=
      Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    rw [hMb]; linarith
  have h3Mb : (3 : ℝ) * Mb ≠ 0 := ne_of_gt (by linarith)
  have harith : Mb * (ε / (3 * Mb)) = ε / 3 := by
    rw [← mul_div_assoc, div_eq_div_iff h3Mb (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  obtain ⟨k, e, c, he, hc, hoverlap⟩ :=
    h Sset (ε / (3 * Mb)) (div_pos hε (by linarith))
  let inclStar := (reducedGroupCStarSubalgebra G).subtype.toNonUnitalStarAlgHom
  let incl : ↥(reducedGroupCStarSubalgebra G) →ₗ[ℂ]
      (GroupHilbert G →L[ℂ] GroupHilbert G) := inclStar
  let down : ↥(reducedGroupCStarSubalgebra G) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) :=
    (compressionLM (folnerIncl e)).comp incl
  let up : (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) →ₗ[ℂ]
      ↥(reducedGroupCStarSubalgebra G) := folnerUpCore e c
  have hsubCP : IsCompletelyPositive incl := by
    dsimp only [incl]
    exact isCompletelyPositive_of_starAlgHom inclStar
  have hdownCP : IsCompletelyPositive down :=
    (isCompletelyPositive_compressionLM (folnerIncl e)).comp
      hsubCP
  have hupCP : IsCompletelyPositive up := isCompletelyPositive_folnerUpCore e c
  have hdownContract : ∀ a, ‖down a‖ ≤ ‖a‖ := by
    intro a
    refine IsCompletelyPositive.norm_apply_le_of_unital
      hdownCP ?_ a
    dsimp only [down, incl, inclStar]
    show compressionLM (folnerIncl e)
      (1 : GroupHilbert G →L[ℂ] GroupHilbert G) = 1
    exact compressionLM_one he
  have hupContract : ∀ d, ‖up d‖ ≤ ‖d‖ := by
    intro d
    show ‖folnerUp e c d‖ ≤ ‖d‖
    exact IsCompletelyPositive.norm_apply_le_of_unital
      (isCompletelyPositive_folnerUp e c) (folnerUp_one e c hc) d
  refine ⟨k, down, up, hdownCP, hupCP, hdownContract, hupContract, ?_⟩
  intro a ha
  ·
    have hγ : ∀ i : Fin (Nn a), GG a i ∈ Sset := by
      intro i
      rw [hSset]
      exact Finset.mem_biUnion.mpr ⟨a, ha,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    have hmass : (∑ i : Fin (Nn a), ‖CC a i‖) ≤ Mb := by
      have hle : (∑ i : Fin (Nn a), ‖CC a i‖)
          ≤ ∑ x ∈ S, ∑ i : Fin (Nn x), ‖CC x i‖ :=
        Finset.single_le_sum
          (f := fun x ↦ ∑ i : Fin (Nn x), ‖CC x i‖)
          (fun x _ ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _) ha
      rw [hMb]; linarith
    let U : Fin (Nn a) → ReducedGroupCStar G := fun i ↦
      ⟨leftRegularOperator G (GG a i), leftRegularOperator_mem_reduced G (GG a i)⟩
    have hspan : ‖a - ∑ i : Fin (Nn a), CC a i • U i‖ ≤ ε / 3 := by
      have hsum : ((∑ i : Fin (Nn a), CC a i • U i : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G) =
            ∑ i : Fin (Nn a), CC a i • leftRegularOperator G (GG a i) := by
        change (reducedGroupCStarSubalgebra G).subtype
          (∑ i : Fin (Nn a), CC a i • U i) = _
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul]; rfl
      calc
        ‖a - ∑ i : Fin (Nn a), CC a i • U i‖ =
            ‖(a : GroupHilbert G →L[ℂ] GroupHilbert G) -
              ((∑ i : Fin (Nn a), CC a i • U i : ReducedGroupCStar G) :
                GroupHilbert G →L[ℂ] GroupHilbert G)‖ := rfl
        _ = ‖(a : GroupHilbert G →L[ℂ] GroupHilbert G) -
              ∑ i : Fin (Nn a), CC a i • leftRegularOperator G (GG a i)‖ := by rw [hsum]
        _ ≤ ε / 3 := (happrox a).le
    have hfix : ∀ i : Fin (Nn a), ‖up (down (U i)) - U i‖ ≤ ε / (3 * Mb) := by
      intro i
      change ‖folnerUp e c (compressionLM (folnerIncl e)
          (leftRegularOperator G (GG a i))) - leftRegularOperator G (GG a i)‖
        ≤ ε / (3 * Mb)
      exact norm_folner_compression_sub_leftRegular_le e c (GG a i)
        (hoverlap _ (hγ i))
    have hthree := norm_comp_sub_le_of_span_approx down up hdownContract hupContract
      (CC a) U a hspan hfix
    have hmassδ : (∑ i : Fin (Nn a), ‖CC a i‖) * (ε / (3 * Mb)) ≤ ε / 3 := by
      calc
        (∑ i : Fin (Nn a), ‖CC a i‖) * (ε / (3 * Mb))
            ≤ Mb * (ε / (3 * Mb)) :=
              mul_le_mul_of_nonneg_right hmass
                (div_nonneg hε.le (by linarith : (0 : ℝ) ≤ 3 * Mb))
        _ = ε / 3 := harith
    change ‖up (down a) - a‖ ≤ ε
    linarith

/-- **Lance's theorem.**  The reduced C⋆-algebra of an amenable group has
the completely positive approximation property. -/
theorem isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable
    (hG : IsAmenable G) : IsNuclearCStarAlgebra (ReducedGroupCStar G) :=
  isNuclearCStarAlgebra_of_overlap fun F _δ hδ ↦
    exists_overlap_of_isAmenable hG F hδ

/-- **The two nuclearity predicates meet.**  The group-flavoured completely
positive approximation property of `Analysis/LanceNuclearity`, tested on
translations, implies the corpus-wide `IsNuclearCStarAlgebra`, tested on
arbitrary elements and with contractivity.

Nothing transports the CPAP's own maps: the premise is turned into an
invariant mean by `hasInvariantMean_of_nuclearReducedCPAP`, and the invariant
mean is turned back into a factorization here.  The two notions therefore meet
through amenability, which is what Lance's theorem says they should do.

The converse is not available; see the module docstring. -/
theorem isNuclearCStarAlgebra_of_nuclearReducedCPAP {Γ : Type} [Group Γ]
    (h : NuclearReducedCPAP Γ) :
    IsNuclearCStarAlgebra (ReducedGroupCStar Γ) :=
  isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable
    (nuclearReducedCPAP_iff_isAmenable.mp h)

/-- **`QuasidiagonalMF.AmenableNuclearInput`, discharged.**  The Lance row of
`metadata/LITERATURE_QUARANTINE.md` is a theorem of this repository. -/
theorem amenableNuclearInput : QuasidiagonalMF.AmenableNuclearInput.{u} where
  nuclear H hgrp hH :=
    @isNuclearCStarAlgebra_reducedGroupCStar_of_isAmenable H hgrp hH

end

end CStarExactness
end GroupApproximation
