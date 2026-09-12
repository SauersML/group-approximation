import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanComplex
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Algebra.AmenableMean
import GroupApproximation.Sofic.AmenableActionSofic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# An infinite group with property `(T)` is not amenable

This module discharges the first of the two classical literature inputs of the
paragraph in `non_mf_group_notes.tex` (locate it by its opening words "The algebra is not
nuclear"; the file is under concurrent edit and line numbers drift):

> The algebra is not nuclear: the canonical map `\mathcal B → E` is injective
> (Section `\ref{sec:literal-presentation}`), so `E` contains an infinite Kazhdan group and is
> nonamenable, whence `\Cred(E)` is not nuclear [Lance].  The nuclear form of
> the Blackadar--Kirchberg problem --- whether every stably finite separable
> nuclear `C^*`-algebra is quasidiagonal --- therefore remains open.

Two classical inputs are used there: nonamenability of infinite Kazhdan
groups, and nonnuclearity of the reduced algebra of a nonamenable group
(Lance).  The first is proved here from scratch, with no hypothesis standing
in for it.  The second is analysed in
`GroupApproximation.Analysis.NuclearityAmenability`.

## The shared first step

`regularRep_hasNoInvariantVectors`.  The left regular representation of an
*infinite* group on real `ℓ²` has no nonzero invariant vector: an invariant
`ℓ²` function is constant on the group, and a nonzero constant is not
square-summable over an infinite index set.  (This is the mechanism the
repository already uses in `KazhdanFiniteGeneration`, there for a coset
space.)  Property `(T)` therefore moves *every* unit vector of `ℓ²(G)`: some
`q` in the Kazhdan control set satisfies `ε ≤ ‖λ q ξ - ξ‖`.

Two independent routes then contradict amenability, one for each of the
repository's two amenability predicates.

## Route 1 (headline): Følner sets, giving `¬ IsAmenable`

`Amenability.IsAmenable` --- a left-invariant finitely additive probability
measure on all subsets --- is the repository's primary predicate, and
`Sofic/AmenableActionSofic.lean` already extracts Følner sets from it via the
repository's Tarski--Hall theorem.  `folnerVec` is the normalized indicator of
such a set, `norm_folnerVec` makes it a unit vector, and
`norm_folner_sub_sq_le` bounds its displacement by the boundary mass.
Symmetrizing the control set before choosing the Følner set makes both `q` and
`q⁻¹` have small boundary, which is exactly the two halves of `A △ qA`.  The
result is `infinite_kazhdan_not_isAmenable`, and
`infinite_kazhdanTextbook_not_isAmenable` restates it from
`HasKazhdanPropertyTComplex` through `hasKazhdanPropertyT_iff_textbook`.

## Route 2 (removed)

An independent second proof via Reiter's condition and Day's argument,
concluding `¬ Amenability.HasInvariantMean` directly and without Følner
sets, was written alongside Route 1 and then removed: it did not compile, and
`HasInvariantMean` implies `IsAmenable` in this repository, so Route 1 already
covers every consequence it had.  Nothing downstream referred to it.  It is
recorded here only so that a reader who finds it in the history knows it was
dropped deliberately rather than lost.

## Transport to the ambient group

`not_isAmenable_of_infinite_kazhdan_subgroup` and
`not_isAmenable_of_infinite_kazhdanTextbook_subgroup` transport nonamenability along an injective homomorphism, which is the
manuscript's own "`E` contains an infinite Kazhdan group and is nonamenable".
This is the repository's `IsAmenable.subgroup` together with
`HasKazhdanPropertyT.of_mulEquiv`.

Nothing here is conditional: the file adds no gaps and no new axioms, and no
hypothesis encodes an unformalized theorem.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace PropertyTNonamenable

open scoped ENNReal
open Amenability KazhdanFiniteGeneration

universe u w

/-! ## Real `ℓ¹` and `ℓ²` of a group -/

section Lp

variable {G : Type u}

/-- The exponent `1` is positive after `ENNReal.toReal`. -/
theorem one_toReal_pos : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num

/-- The exponent `2` is positive after `ENNReal.toReal`. -/
theorem two_toReal_pos : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num

/-- The `ℓ¹` norm is the unordered sum of the absolute values. -/
theorem hasSum_abs_l1 (f : lp (fun _ : G ↦ ℝ) 1) :
    HasSum (fun x : G ↦ |f x|) ‖f‖ := by
  have h := lp.hasSum_norm one_toReal_pos f
  have hone : ((1 : ℝ≥0∞).toReal) = (1 : ℝ) := ENNReal.toReal_one
  have hfun : (fun i : G ↦ ‖f i‖ ^ (1 : ℝ≥0∞).toReal) = fun i : G ↦ |f i| := by
    funext i
    rw [hone, Real.rpow_one, Real.norm_eq_abs]
  have hval : ‖f‖ ^ (1 : ℝ≥0∞).toReal = ‖f‖ := by
    rw [hone, Real.rpow_one]
  rw [hfun, hval] at h
  exact h

/-- The square of the `ℓ²` norm is the unordered sum of the squares. -/
theorem hasSum_sq_l2 (f : lp (fun _ : G ↦ ℝ) 2) :
    HasSum (fun x : G ↦ (f x) ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm two_toReal_pos f
  have htwo : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
  have hfun : (fun i : G ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)
      = fun i : G ↦ (f i) ^ 2 := by
    funext i
    rw [htwo, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hval : ‖f‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ 2 := by
    rw [htwo, Real.rpow_two]
  rw [hfun, hval] at h
  exact h

end Lp



/-! ## The left regular representation -/

section Regular

variable {G : Type u} [Group G]

/-- **Step 1.** The left regular representation of an infinite group has no
nonzero invariant vector: an invariant `ℓ²` function is constant on the group,
and a nonzero constant is not square summable over an infinite set. -/
theorem regularRep_hasNoInvariantVectors [Infinite G] :
    IsKazhdanPair.HasNoInvariantVectors G (permutationRepresentation G G) := by
  intro y hy
  have hconst : ∀ b : G, y b = y 1 := by
    intro b
    have h := congrArg (fun z : lp (fun _ : G ↦ ℝ) 2 ↦ z b) (hy b)
    change y ((MulAction.toPerm b).symm b) = y b at h
    have hb : ((MulAction.toPerm b).symm b : G) = 1 := by
      change b⁻¹ • b = (1 : G)
      rw [smul_eq_mul, inv_mul_cancel]
    rw [hb] at h
    exact h.symm
  by_contra hy0
  have hc : y 1 ≠ 0 := by
    intro h0
    apply hy0
    apply lp.ext
    funext b
    rw [hconst b, h0]
    rfl
  have hsum : Summable fun b : G ↦ ‖y b‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff two_toReal_pos).1 (lp.memℓp y)
  rw [show (fun b : G ↦ ‖y b‖ ^ (2 : ℝ≥0∞).toReal) =
      fun _ : G ↦ ‖y 1‖ ^ (2 : ℝ≥0∞).toReal from
    funext fun b ↦ by rw [hconst b]] at hsum
  haveI : Finite G :=
    Finite.of_summable_const (Real.rpow_pos_of_pos (norm_pos_iff.2 hc) _) hsum
  exact not_finite G

end Regular

/-! ## Følner sets give almost invariant vectors

`Algebra/Amenable.lean` takes amenability in the finitely-additive-measure
form `Amenability.IsAmenable`, and `Sofic/AmenableActionSofic.lean` already
extracts Følner sets from it (`AmenableActionSofic.exists_folner`, through the
repository's Tarski--Hall theorem).  That is everything this route needs: the
normalized indicator of a Følner set is an almost invariant unit vector of the
left regular representation, which property `(T)` forbids on an infinite
group.  This is the short path to the manuscript's statement, and it lands on
the repository's *primary* amenability predicate.

The control set is symmetrized before the Følner set is chosen, so that both
`q` and `q⁻¹` have small boundary: the two one-sided boundaries
`boundary A q⁻¹` and `boundary A q` are exactly the two halves of the
symmetric difference `A △ qA`, which is where the translate of the indicator
differs from it. -/

section Folner

variable {G : Type u} [Group G] [DecidableEq G]

/-- The normalizing constant `|A|^(-1/2)` of the indicator of a finite set. -/
noncomputable def folnerCoeff (A : Finset G) : ℝ := Real.sqrt ((A.card : ℝ)⁻¹)

omit [Group G] [DecidableEq G] in
theorem folnerCoeff_nonneg (A : Finset G) : 0 ≤ folnerCoeff A :=
  Real.sqrt_nonneg _

omit [Group G] [DecidableEq G] in
theorem folnerCoeff_sq (A : Finset G) : folnerCoeff A ^ 2 = (A.card : ℝ)⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg _))

omit [Group G] in
/-- The normalized indicator of a finite set is square summable. -/
theorem memℓp_folner (A : Finset G) :
    Memℓp (fun x : G ↦ if x ∈ A then folnerCoeff A else 0) 2 := by
  apply memℓp_gen
  refine summable_of_ne_finset_zero (s := A) fun b hb ↦ ?_
  have htwo : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
  rw [if_neg hb, norm_zero, htwo, Real.rpow_two]
  norm_num

/-- The normalized indicator of a finite set, as a vector of real `ℓ²`. -/
noncomputable def folnerVec (A : Finset G) : lp (fun _ : G ↦ ℝ) 2 :=
  ⟨fun x : G ↦ if x ∈ A then folnerCoeff A else 0, memℓp_folner A⟩

omit [Group G] in
@[simp] theorem folnerVec_apply (A : Finset G) (x : G) :
    folnerVec A x = if x ∈ A then folnerCoeff A else 0 := rfl

omit [Group G] in
/-- The normalized indicator of a nonempty finite set is a unit vector. -/
theorem norm_folnerVec (A : Finset G) (hA : A.Nonempty) :
    ‖folnerVec A‖ = 1 := by
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  have hfin : HasSum (fun x : G ↦ (folnerVec A x) ^ 2)
      (∑ x ∈ A, (folnerVec A x) ^ 2) := by
    refine hasSum_sum_of_ne_finset_zero (s := A) fun b hb ↦ ?_
    show (folnerVec A b) ^ 2 = 0
    rw [folnerVec_apply, if_neg hb]
    norm_num
  have hsq : ‖folnerVec A‖ ^ 2 = ∑ x ∈ A, (folnerVec A x) ^ 2 :=
    (hasSum_sq_l2 (folnerVec A)).unique hfin
  have hval : ∑ x ∈ A, (folnerVec A x) ^ 2 = 1 := by
    have hcongr : ∑ x ∈ A, (folnerVec A x) ^ 2 = ∑ _x ∈ A, folnerCoeff A ^ 2 :=
      Finset.sum_congr rfl fun x hx ↦ by rw [folnerVec_apply, if_pos hx]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, folnerCoeff_sq,
      mul_inv_cancel₀ hcard.ne']
  rw [hval] at hsq
  have hn : (0 : ℝ) ≤ ‖folnerVec A‖ := norm_nonneg _
  have hfac : (‖folnerVec A‖ - 1) * (‖folnerVec A‖ + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · linarith

/-- The finite set outside which left translation by `q` does not move the
normalized indicator of `A`: the two one-sided boundaries of `A`. -/
noncomputable def folnerDefect (A : Finset G) (q : G) : Finset G :=
  AmenableActionSofic.boundary A q⁻¹ ∪
    (AmenableActionSofic.boundary A q).image (fun a ↦ q * a)

theorem card_folnerDefect_le (A : Finset G) (q : G) :
    (folnerDefect A q).card
      ≤ (AmenableActionSofic.boundary A q⁻¹).card
        + (AmenableActionSofic.boundary A q).card :=
  (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_image_le _)

/-- Off the defect set the translate of the normalized indicator agrees with
it. -/
theorem folnerVec_translate_eq (A : Finset G) (q x : G)
    (hx : x ∉ folnerDefect A q) :
    folnerVec A (q⁻¹ * x) = folnerVec A x := by
  have hinv : q * (q⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hmem : (q⁻¹ * x ∈ A) ↔ (x ∈ A) := by
    constructor
    · intro hin
      by_contra hout
      refine hx (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨q⁻¹ * x, ?_, hinv⟩))
      refine AmenableActionSofic.mem_boundary.mpr ⟨hin, ?_⟩
      rw [hinv]
      exact hout
    · intro hin
      by_contra hout
      exact hx (Finset.mem_union_left _
        (AmenableActionSofic.mem_boundary.mpr ⟨hin, hout⟩))
  rw [folnerVec_apply, folnerVec_apply]
  by_cases h : x ∈ A
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg fun hc ↦ h (hmem.mp hc), if_neg h]

/-- Every coordinate of the displacement is bounded by the normalizing
constant. -/
theorem folnerVec_sub_sq_le (A : Finset G) (q x : G) :
    ((permutationRepresentation G G q (folnerVec A) - folnerVec A) x) ^ 2
      ≤ folnerCoeff A ^ 2 := by
  have hval : (permutationRepresentation G G q (folnerVec A) - folnerVec A) x
      = folnerVec A (q⁻¹ * x) - folnerVec A x := by
    rw [lp.coeFn_sub, Pi.sub_apply, permutationRepresentation_apply, smul_eq_mul]
  rw [hval, folnerVec_apply, folnerVec_apply]
  split_ifs <;> nlinarith [sq_nonneg (folnerCoeff A)]

/-- **The Følner estimate.**  The squared displacement of the normalized
indicator is the boundary mass. -/
theorem norm_folner_sub_sq_le (A : Finset G) (q : G) :
    ‖permutationRepresentation G G q (folnerVec A) - folnerVec A‖ ^ 2
      ≤ (((AmenableActionSofic.boundary A q⁻¹).card : ℝ)
          + ((AmenableActionSofic.boundary A q).card : ℝ)) * folnerCoeff A ^ 2 := by
  have hval : ∀ x : G,
      (permutationRepresentation G G q (folnerVec A) - folnerVec A) x
        = folnerVec A (q⁻¹ * x) - folnerVec A x := by
    intro x
    rw [lp.coeFn_sub, Pi.sub_apply, permutationRepresentation_apply, smul_eq_mul]
  have hfin : HasSum
      (fun x : G ↦
        ((permutationRepresentation G G q (folnerVec A) - folnerVec A) x) ^ 2)
      (∑ x ∈ folnerDefect A q,
        ((permutationRepresentation G G q (folnerVec A) - folnerVec A) x) ^ 2) := by
    refine hasSum_sum_of_ne_finset_zero (s := folnerDefect A q) fun b hb ↦ ?_
    show ((permutationRepresentation G G q (folnerVec A) - folnerVec A) b) ^ 2 = 0
    rw [hval b, folnerVec_translate_eq A q b hb]
    simp
  have hsq :
      ‖permutationRepresentation G G q (folnerVec A) - folnerVec A‖ ^ 2
        = ∑ x ∈ folnerDefect A q,
            ((permutationRepresentation G G q (folnerVec A) - folnerVec A) x) ^ 2 :=
    (hasSum_sq_l2 _).unique hfin
  have hcast : ((folnerDefect A q).card : ℝ)
      ≤ ((AmenableActionSofic.boundary A q⁻¹).card : ℝ)
        + ((AmenableActionSofic.boundary A q).card : ℝ) := by
    exact_mod_cast card_folnerDefect_le A q
  rw [hsq]
  calc ∑ x ∈ folnerDefect A q,
        ((permutationRepresentation G G q (folnerVec A) - folnerVec A) x) ^ 2
      ≤ ∑ _x ∈ folnerDefect A q, folnerCoeff A ^ 2 :=
        Finset.sum_le_sum fun x _ ↦ folnerVec_sub_sq_le A q x
    _ = ((folnerDefect A q).card : ℝ) * folnerCoeff A ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((AmenableActionSofic.boundary A q⁻¹).card : ℝ)
          + ((AmenableActionSofic.boundary A q).card : ℝ)) * folnerCoeff A ^ 2 :=
        mul_le_mul_of_nonneg_right hcast (sq_nonneg _)

end Folner



/-! ## The theorem -/

section Main

variable {G : Type u} [Group G]

/-- **An infinite group with property `(T)` is not amenable.**

This is the manuscript's first classical input, "nonamenability of infinite
Kazhdan groups", proved rather than cited, and stated for
`Amenability.IsAmenable` --- the repository's primary amenability predicate, a
left-invariant finitely additive probability measure on all subsets.

The proof is the classical one.  Amenability supplies a Følner set `A` for the
symmetrized Kazhdan control set; its normalized indicator is a unit vector of
`ℓ²(G)` displaced by less than `ε` by every element of the control set; the
Kazhdan pair therefore produces a nonzero invariant vector, which an infinite
group's regular representation does not have. -/
theorem infinite_kazhdan_not_isAmenable [Infinite G]
    (hT : HasKazhdanPropertyT.{u, u} G) : ¬ IsAmenable G := by
  classical
  intro hA
  obtain ⟨Q, ε, hpair⟩ := hT
  have hε : 0 < ε := hpair.1
  have hδ : (0 : ℝ) < ε ^ 2 / 2 := div_pos (pow_pos hε 2) (by norm_num)
  obtain ⟨A, hAne, hsmall⟩ :=
    AmenableActionSofic.exists_folner hA (Q ∪ Q.image (fun g ↦ g⁻¹)) hδ
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAne
  obtain ⟨q, hq, hmove⟩ :=
    IsKazhdanPair.exists_moved_of_noInvariant hpair (permutationRepresentation G G)
      regularRep_hasNoInvariantVectors (folnerVec A) (norm_folnerVec A hAne)
  have hb1 := hsmall q (Finset.mem_union_left _ hq)
  have hb2 := hsmall q⁻¹
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
  have hbound := norm_folner_sub_sq_le A q
  rw [folnerCoeff_sq] at hbound
  have hlt :
      ‖permutationRepresentation G G q (folnerVec A) - folnerVec A‖ ^ 2 < ε ^ 2 := by
    refine lt_of_le_of_lt hbound ?_
    have hsum : ((AmenableActionSofic.boundary A q⁻¹).card : ℝ)
        + ((AmenableActionSofic.boundary A q).card : ℝ) < ε ^ 2 * (A.card : ℝ) := by
      linarith
    calc (((AmenableActionSofic.boundary A q⁻¹).card : ℝ)
          + ((AmenableActionSofic.boundary A q).card : ℝ)) * (A.card : ℝ)⁻¹
        < ε ^ 2 * (A.card : ℝ) * (A.card : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_right hsum (inv_pos.mpr hcard)
      _ = ε ^ 2 := by rw [mul_assoc, mul_inv_cancel₀ hcard.ne', mul_one]
  have hge : ε ^ 2 ≤
      ‖permutationRepresentation G G q (folnerVec A) - folnerVec A‖ ^ 2 := by
    have hmm := mul_self_le_mul_self hε.le hmove
    rw [pow_two, pow_two]
    exact hmm
  linarith

/-- The same statement from the textbook complex-unitary form of property
`(T)` at an arbitrary representation universe.  This is the shape in which the
repository states its property-`(T)` certificates, so it is the form that
plugs directly into the existing development. -/
theorem infinite_kazhdanTextbook_not_isAmenable [Infinite G]
    (hT : HasKazhdanPropertyTComplex.{u, max u w} G) : ¬ IsAmenable G :=
  infinite_kazhdan_not_isAmenable (hasKazhdanPropertyT_iff_textbook.mpr hT)

end Main


/-! ## The manuscript step -/

section Manuscript

/-- **The manuscript step**, in the repository's primary amenability
predicate.  If a group contains an isomorphic copy of an infinite group with
property `(T)`, it is not amenable.  With `H = \mathcal B` and `G = E` this is
the manuscript's "*the canonical map `\mathcal B → E` is injective, so `E`
contains an infinite Kazhdan group and is nonamenable*".

Only the repository's own permanence properties are used: amenability passes
to subgroups (`Amenability.IsAmenable.subgroup`) and property `(T)` passes
along isomorphisms (`HasKazhdanPropertyT.of_mulEquiv`). -/
theorem not_isAmenable_of_infinite_kazhdan_subgroup {G H : Type u} [Group G]
    [Group H] [Infinite H] (hT : HasKazhdanPropertyT.{u, u} H) (f : H →* G)
    (hf : Function.Injective f) : ¬ IsAmenable G := by
  intro hG
  haveI : Infinite ↥f.range :=
    Infinite.of_injective (MonoidHom.ofInjective hf)
      (MonoidHom.ofInjective hf).injective
  have hTr : HasKazhdanPropertyT.{u, u} ↥f.range :=
    HasKazhdanPropertyT.of_mulEquiv (MonoidHom.ofInjective hf).symm hT
  exact infinite_kazhdan_not_isAmenable hTr (hG.subgroup f.range)

/-- The same step from the textbook complex-unitary form of property `(T)`. -/
theorem not_isAmenable_of_infinite_kazhdanTextbook_subgroup {G H : Type u}
    [Group G] [Group H] [Infinite H]
    (hT : HasKazhdanPropertyTComplex.{u, max u w} H) (f : H →* G)
    (hf : Function.Injective f) : ¬ IsAmenable G :=
  not_isAmenable_of_infinite_kazhdan_subgroup
    (hasKazhdanPropertyT_iff_textbook.mpr hT) f hf

end Manuscript

end PropertyTNonamenable
end GroupApproximation
