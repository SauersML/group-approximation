import GroupApproximation.Leavitt.LeavittNormalForm
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEJZInstance
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceTauWhiteheadConclusionClosure
import GroupApproximation.PropertyT.FinitelyGeneratedRing

/-!
# Exact sentence closure for the current Leavitt-compression proof

This file isolates the four pieces of the current manuscript section that
were not previously available as literal sentence-level declarations:

* the notation `I = I₆` used in the Whitehead word;
* the two ordered products of the thirty-six elementary matrices obtained by
  inserting the entries of a `6 × 6` block;
* generation of the concrete binary Leavitt algebra by the four named
  generators, both as an algebra and as a unital ring; and
* the whole property-`(T)` and one-sided-compression proposition.

The entry products use the row-major order supplied by `indices6.flatMap`.
The manuscript leaves the order of `∏_{r,s}` unspecified because all cross
products vanish; fixing this order makes the displayed products literal in
Lean without adding any commutativity hypothesis to the coefficient ring.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped BigOperators

/-! ## `I = I₆` -/

/-- The matrix denoted by `I` in the printed Whitehead factorization. -/
abbrev manuscriptWhiteheadI : Matrix (Fin 6) (Fin 6) R := 1

/-- **“Put `I = I₆`.”** -/
theorem manuscriptWhiteheadI_eq_identitySix :
    manuscriptWhiteheadI = (1 : Matrix (Fin 6) (Fin 6) R) :=
  rfl

/-! ## Literal entry-by-entry products -/

/-- The six indices, in the order `0,1,…,5`. -/
private def indices6 : List (Fin 6) := List.ofFn id

/-- The inclusion of the first six coordinates into the twelve-coordinate
Whitehead frame. -/
private def firstSix (r : Fin 6) : Fin 12 :=
  ⟨r.val, by omega⟩

/-- The inclusion of the last six coordinates into the twelve-coordinate
Whitehead frame. -/
private def lastSix (s : Fin 6) : Fin 12 :=
  ⟨6 + s.val, by omega⟩

private theorem firstSix_ne_lastSix (r s : Fin 6) : firstSix r ≠ lastSix s := by
  intro h
  have hval := congrArg Fin.val h
  simp [firstSix, lastSix] at hval
  omega

private theorem lastSix_ne_firstSix (r s : Fin 6) : lastSix r ≠ firstSix s := by
  exact (firstSix_ne_lastSix s r).symm

/-- The thirty-six upper-right single-entry matrices, in row-major order. -/
private def upperEntryMatrices (B : Matrix (Fin 6) (Fin 6) R) :
    List (Matrix (Fin 12) (Fin 12) R) :=
  indices6.flatMap fun r ↦
    indices6.map fun s ↦ Matrix.single (firstSix r) (lastSix s) (B r s)

/-- The thirty-six lower-left single-entry matrices, in row-major order. -/
private def lowerEntryMatrices (B : Matrix (Fin 6) (Fin 6) R) :
    List (Matrix (Fin 12) (Fin 12) R) :=
  indices6.flatMap fun r ↦
    indices6.map fun s ↦ Matrix.single (lastSix r) (firstSix s) (B r s)

/-- The literal elementary factors in the first product printed after the
Whitehead factorization. -/
def manuscriptUpperEntryFactors (B : Matrix (Fin 6) (Fin 6) R) :
    List (Matrix (Fin 12) (Fin 12) R)ˣ :=
  indices6.flatMap fun r ↦
    indices6.map fun s ↦
      elementaryUnit (firstSix r) (lastSix s) (firstSix_ne_lastSix r s) (B r s)

/-- The literal elementary factors in the second product printed after the
Whitehead factorization. -/
def manuscriptLowerEntryFactors (B : Matrix (Fin 6) (Fin 6) R) :
    List (Matrix (Fin 12) (Fin 12) R)ˣ :=
  indices6.flatMap fun r ↦
    indices6.map fun s ↦
      elementaryUnit (lastSix r) (firstSix s) (lastSix_ne_firstSix r s) (B r s)

/-- The upper block-unipotent matrix `[[I,B],[0,I]]`, written entrywise in
the literal twelve-coordinate frame. -/
def manuscriptUpperBlockUnipotent (B : Matrix (Fin 6) (Fin 6) R) :
    Matrix (Fin 12) (Fin 12) R :=
  1 + (upperEntryMatrices B).sum

/-- The lower block-unipotent matrix `[[I,0],[B,I]]`, written entrywise in
the literal twelve-coordinate frame. -/
def manuscriptLowerBlockUnipotent (B : Matrix (Fin 6) (Fin 6) R) :
    Matrix (Fin 12) (Fin 12) R :=
  1 + (lowerEntryMatrices B).sum

private theorem unitsVal_listProd {A : Type*} [Monoid A] (xs : List Aˣ) :
    ((xs.prod : Aˣ) : A) = (xs.map fun x ↦ (x : A)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem mul_listSum_eq_zero {A : Type*} [Ring A] (x : A)
    (xs : List A) (h : ∀ y ∈ xs, x * y = 0) : x * xs.sum = 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      rw [List.sum_cons, mul_add, h y (by simp)]
      rw [ih (fun z hz ↦ h z (by simp [hz]))]
      exact add_zero 0

private theorem listProd_one_add_eq_one_add_sum {A : Type*} [Ring A]
    (xs : List A) (h : ∀ x ∈ xs, ∀ y ∈ xs, x * y = 0) :
    (xs.map fun x ↦ 1 + x).prod = 1 + xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail : ∀ y ∈ xs, ∀ z ∈ xs, y * z = 0 := by
        intro y hy z hz
        exact h y (by simp [hy]) z (by simp [hz])
      have hxsum : x * xs.sum = 0 :=
        mul_listSum_eq_zero x xs (fun y hy ↦ h x (by simp) y (by simp [hy]))
      rw [List.map_cons, List.prod_cons, ih htail, List.sum_cons]
      noncomm_ring [hxsum]

private theorem upperEntryMatrices_pairwiseZero
    (B : Matrix (Fin 6) (Fin 6) R) :
    ∀ X ∈ upperEntryMatrices B, ∀ Y ∈ upperEntryMatrices B, X * Y = 0 := by
  intro X hX Y hY
  simp only [upperEntryMatrices, List.mem_flatMap, List.mem_map] at hX hY
  obtain ⟨r, -, s, -, rfl⟩ := hX
  obtain ⟨u, -, v, -, rfl⟩ := hY
  exact Matrix.single_mul_single_of_ne
    (c := B r s) (firstSix r) (lastSix s) (firstSix u)
      (firstSix_ne_lastSix u s).symm (B u v)

private theorem lowerEntryMatrices_pairwiseZero
    (B : Matrix (Fin 6) (Fin 6) R) :
    ∀ X ∈ lowerEntryMatrices B, ∀ Y ∈ lowerEntryMatrices B, X * Y = 0 := by
  intro X hX Y hY
  simp only [lowerEntryMatrices, List.mem_flatMap, List.mem_map] at hX hY
  obtain ⟨r, -, s, -, rfl⟩ := hX
  obtain ⟨u, -, v, -, rfl⟩ := hY
  exact Matrix.single_mul_single_of_ne
    (c := B r s) (lastSix r) (firstSix s) (lastSix u)
      (lastSix_ne_firstSix u s).symm (B u v)

private theorem upperFactors_values (B : Matrix (Fin 6) (Fin 6) R) :
    (manuscriptUpperEntryFactors B).map
        (fun x ↦ (x : Matrix (Fin 12) (Fin 12) R)) =
      (upperEntryMatrices B).map (fun X ↦ 1 + X) := by
  simp only [manuscriptUpperEntryFactors, upperEntryMatrices,
    List.map_flatMap, List.map_map]
  rfl

private theorem lowerFactors_values (B : Matrix (Fin 6) (Fin 6) R) :
    (manuscriptLowerEntryFactors B).map
        (fun x ↦ (x : Matrix (Fin 12) (Fin 12) R)) =
      (lowerEntryMatrices B).map (fun X ↦ 1 + X) := by
  simp only [manuscriptLowerEntryFactors, lowerEntryMatrices,
    List.map_flatMap, List.map_map]
  rfl

/-- **The first displayed product.**  In the fixed row-major order,
`[[I,B],[0,I]]` is the product of the thirty-six matrices
`e_{r,6+s}(b_rs)`. -/
def UpperBlockUnipotentOrderedEntryProduct : Prop :=
  ∀ B : Matrix (Fin 6) (Fin 6) R,
    manuscriptUpperBlockUnipotent B =
      ((manuscriptUpperEntryFactors B).prod :
        (Matrix (Fin 12) (Fin 12) R)ˣ)

theorem manuscriptUpperBlockUnipotent_eq_orderedEntryProduct :
    UpperBlockUnipotentOrderedEntryProduct := by
  intro B
  rw [manuscriptUpperBlockUnipotent, unitsVal_listProd,
    upperFactors_values]
  exact (listProd_one_add_eq_one_add_sum
    (upperEntryMatrices B) (upperEntryMatrices_pairwiseZero B)).symm

/-- **The second displayed product.**  In the fixed row-major order,
`[[I,0],[B,I]]` is the product of the thirty-six matrices
`e_{6+r,s}(b_rs)`. -/
def LowerBlockUnipotentOrderedEntryProduct : Prop :=
  ∀ B : Matrix (Fin 6) (Fin 6) R,
    manuscriptLowerBlockUnipotent B =
      ((manuscriptLowerEntryFactors B).prod :
        (Matrix (Fin 12) (Fin 12) R)ˣ)

theorem manuscriptLowerBlockUnipotent_eq_orderedEntryProduct :
    LowerBlockUnipotentOrderedEntryProduct := by
  intro B
  rw [manuscriptLowerBlockUnipotent, unitsVal_listProd,
    lowerFactors_values]
  exact (listProd_one_add_eq_one_add_sum
    (lowerEntryMatrices B) (lowerEntryMatrices_pairwiseZero B)).symm

/-! ## Generation by the four named Leavitt generators -/

/-- The exact four-element set named in the manuscript. -/
def manuscriptLeavittGeneratorSet : Set R :=
  {leavittFamily.s0, leavittFamily.s1, leavittFamily.t0, leavittFamily.t1}

private theorem range_generator_eq_manuscriptLeavittGeneratorSet :
    Set.range (BinaryLeavitt.generator (ZMod 2)) =
      manuscriptLeavittGeneratorSet := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    fin_cases g <;>
      simp [manuscriptLeavittGeneratorSet, leavittFamily,
        UniversalLeavitt.family, BinaryLeavitt.family,
        BinaryLeavitt.s0, BinaryLeavitt.s1, BinaryLeavitt.t0, BinaryLeavitt.t1]
  · intro hx
    simp only [manuscriptLeavittGeneratorSet, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · exact ⟨BinaryLeavitt.s0, h.symm⟩
    · exact ⟨BinaryLeavitt.s1, h.symm⟩
    · exact ⟨BinaryLeavitt.t0, h.symm⟩
    · exact ⟨BinaryLeavitt.t1, h.symm⟩

/-- The four named elements generate `R` as a unital `F₂`-algebra. -/
theorem manuscriptLeavittNamedGenerators_adjoin_eq_top :
    Algebra.adjoin (ZMod 2) manuscriptLeavittGeneratorSet = ⊤ := by
  rw [← range_generator_eq_manuscriptLeavittGeneratorSet]
  exact BinaryLeavitt.adjoin_range_generator (ZMod 2)

/-- **“The ring `R` is generated by `s₀,s₁,t₀,t₁` as a unital
ring.”**  This is the literal unital-subring formulation. -/
theorem manuscriptLeavittNamedGenerators_subringClosure_eq_top :
    Subring.closure manuscriptLeavittGeneratorSet = ⊤ := by
  rw [Subring.eq_top_iff']
  intro x
  apply (mem_adjoin_iff_mem_closure
    (fun r T ↦ algebraMap_zmod_mem_subring 2 r T)
    manuscriptLeavittGeneratorSet x).1
  rw [manuscriptLeavittNamedGenerators_adjoin_eq_top]
  exact Algebra.mem_top

/-- The exact bridge used in the next property-`(T)` sentence: the named
four-generator statement implies Mathlib's finite-type formulation. -/
theorem manuscriptLeavittNamedGeneration_finiteTypeBridge :
    Subring.closure manuscriptLeavittGeneratorSet = ⊤ ∧
      Algebra.adjoin (ZMod 2) manuscriptLeavittGeneratorSet = ⊤ ∧
      Algebra.FiniteType (ZMod 2) R :=
  ⟨manuscriptLeavittNamedGenerators_subringClosure_eq_top,
    manuscriptLeavittNamedGenerators_adjoin_eq_top,
    coefficientRing_finiteType⟩

/-! ## The whole compression proposition -/

/-- **The complete proposition `prop:leavitt-compression`.**  Both exact
groups have property `(T)`; the displayed `tau` belongs to `H`; and
conjugation by it carries the upper-left `EL₃(R)` corner into itself. -/
theorem manuscriptCurrentLeavittCompressionProposition :
    HasKazhdanPropertyT.{0, 0} H ∧
      HasKazhdanPropertyT.{0, 0} corner ∧
      printedTauGL ∈ elementaryGroup (Fin 12) R ∧
      (∀ gamma ∈ corner, tau * gamma * tau⁻¹ ∈ corner) := by
  exact ⟨printedBothGroupsHaveKazhdanPropertyT.1,
    printedBothGroupsHaveKazhdanPropertyT.2,
    printedTauGL_mem,
    tau_compresses_corner⟩

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoint

#audit_closed_axioms manuscriptWhiteheadI_eq_identitySix
#audit_closed_axioms manuscriptUpperBlockUnipotent_eq_orderedEntryProduct
#audit_closed_axioms manuscriptLowerBlockUnipotent_eq_orderedEntryProduct
#audit_closed_axioms manuscriptLeavittNamedGenerators_adjoin_eq_top
#audit_closed_axioms manuscriptLeavittNamedGenerators_subringClosure_eq_top
#audit_closed_axioms manuscriptLeavittNamedGeneration_finiteTypeBridge
#audit_closed_axioms manuscriptCurrentLeavittCompressionProposition
