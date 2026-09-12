import GroupApproximation.GGT.HullSCLemma44PrefixFan

/-!
# The bounded cell presentation behind the prefix fan

The free-group fan uses two sorts of bounded cells.  Literal prefix triangles
have length three.  Two-letter inverse cells identify the positive relative
letter named by `x⁻¹` with the formal inverse of the letter named by `x`.

This file proves that their union is a strongly bounded family of admissible
identity words for the prefix quotient.  It also preserves the finite
peripheral support from the original Hull input: inverse cells contain only
base letters, so they add no peripheral component labels.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

/-! ## Inverse-pair relations -/

/-- Membership in the inverse-pair family with its relator step displayed. -/
theorem RelWord.mem_prefixInversePairs
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {pair : List (GGT.RelLetter Q Lambda)} :
    pair ∈ RelWord.prefixInversePairs W q ↔
      ∃ word ∈ W, ∃ pre a suffix,
        word = pre ++ a :: suffix ∧ pair = prefixInversePair q pre a :=
  Iff.rfl

/-- Every inverse-pair relation has length two. -/
theorem RelWord.length_eq_two_of_mem_prefixInversePairs
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {pair : List (GGT.RelLetter Q Lambda)}
    (hpair : pair ∈ RelWord.prefixInversePairs W q) :
    pair.length = 2 := by
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := hpair
  exact prefixInversePair_length q pre a

/-- Every inverse-pair relation spells the identity. -/
theorem RelWord.listVal_eq_one_of_mem_prefixInversePairs
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {pair : List (GGT.RelLetter Q Lambda)}
    (hpair : pair ∈ RelWord.prefixInversePairs W q) :
    GGT.RelLetter.listVal pair = 1 := by
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := hpair
  exact prefixInversePair_value q pre a

/-- Inverse-pair relations contain no peripheral component letters. -/
theorem RelWord.componentSupport_prefixInversePairs_eq_empty
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) :
    RelWord.componentSupport (RelWord.prefixInversePairs W q) = ∅ := by
  ext b
  constructor
  · rintro ⟨⟨lam, h, rfl⟩, pair, hpair, hmem⟩
    obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := hpair
    simp only [prefixInversePair, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with hmem | hmem <;> cases hmem
  · intro h
    exact h.elim

/-- A displayed inverse pair is legal over the quotient prefix relative
generating set. -/
theorem prefixInversePair_admissible
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    {word pre suffix : List (GGT.RelLetter G Lambda)}
    {a : GGT.RelLetter G Lambda}
    (hword : word ∈ W) (hsplit : word = pre ++ a :: suffix) :
    RelWord.IsAdmissible (D.prefixQuotient W hsc q hq)
      (prefixInversePair q pre a) := by
  obtain ⟨hpre, hnext⟩ :=
    GGT.RelGenSet.prefixValues_of_step hword hsplit
  intro b hb
  simp only [prefixInversePair, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl
  · exact D.map_prefixValue_mem_prefixQuotient_base W hsc q hq hnext
  · change (q (GGT.RelLetter.listVal (pre ++ [a])))⁻¹ ∈
      (D.prefixQuotient W hsc q hq).base
    simpa only [map_inv] using
      D.map_prefixValue_mem_prefixQuotient_base W hsc q hq
        (RelWord.inv_mem_prefixValues hsc hnext)

/-- Every inverse-pair relation in the family is legal. -/
theorem RelWord.admissible_of_mem_prefixInversePairs
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    {pair : List (GGT.RelLetter Q Lambda)}
    (hpair : pair ∈ RelWord.prefixInversePairs W q) :
    RelWord.IsAdmissible (D.prefixQuotient W hsc q hq) pair := by
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := hpair
  exact prefixInversePair_admissible hsc q hq hword hsplit

/-! ## The combined bounded family -/

/-- Component support distributes over a union of relation families. -/
theorem RelWord.componentSupport_union
    {G : Type u} {Lambda : Type w}
    (V U : Set (List (GGT.RelLetter G Lambda))) :
    RelWord.componentSupport (V ∪ U) =
      RelWord.componentSupport V ∪ RelWord.componentSupport U := by
  ext a
  constructor
  · rintro ⟨hcomp, word, hword, ha⟩
    rcases hword with hword | hword
    · exact Or.inl ⟨hcomp, word, hword, ha⟩
    · exact Or.inr ⟨hcomp, word, hword, ha⟩
  · rintro (ha | ha)
    · obtain ⟨hcomp, word, hword, haword⟩ := ha
      exact ⟨hcomp, word, Or.inl hword, haword⟩
    · obtain ⟨hcomp, word, hword, haword⟩ := ha
      exact ⟨hcomp, word, Or.inr hword, haword⟩

/-- Every combined prefix-presentation cell has length at most three. -/
theorem RelWord.length_le_three_of_mem_prefixPresentationCells
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {cell : List (GGT.RelLetter Q Lambda)}
    (hcell : cell ∈ RelWord.prefixPresentationCells W q) :
    cell.length ≤ 3 := by
  rcases hcell with hcell | hcell
  · rw [RelWord.length_eq_three_of_mem_prefixTriangles hcell]
  · rw [RelWord.length_eq_two_of_mem_prefixInversePairs hcell]
    omega

/-- Every combined prefix-presentation cell spells the identity. -/
theorem RelWord.listVal_eq_one_of_mem_prefixPresentationCells
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {cell : List (GGT.RelLetter Q Lambda)}
    (hcell : cell ∈ RelWord.prefixPresentationCells W q) :
    GGT.RelLetter.listVal cell = 1 := by
  rcases hcell with hcell | hcell
  · exact RelWord.listVal_eq_one_of_mem_prefixTriangles hcell
  · exact RelWord.listVal_eq_one_of_mem_prefixInversePairs hcell

/-- Every combined prefix-presentation cell is legal. -/
theorem RelWord.admissible_of_mem_prefixPresentationCells
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    {cell : List (GGT.RelLetter Q Lambda)}
    (hcell : cell ∈ RelWord.prefixPresentationCells W q) :
    RelWord.IsAdmissible (D.prefixQuotient W hsc q hq) cell := by
  rcases hcell with hcell | hcell
  · exact RelWord.admissible_of_mem_prefixTriangles hsc q hq hcell
  · exact RelWord.admissible_of_mem_prefixInversePairs hsc q hq hcell

/-- The combined cell family has finite peripheral component support. -/
theorem RelWord.componentSupport_prefixPresentationCells_finite
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) :
    (RelWord.componentSupport
      (RelWord.prefixPresentationCells W q)).Finite := by
  change (RelWord.componentSupport
    (RelWord.prefixTriangles W q ∪ RelWord.prefixInversePairs W q)).Finite
  rw [RelWord.componentSupport_union,
    RelWord.componentSupport_prefixInversePairs_eq_empty]
  simpa only [Set.union_empty] using
    RelWord.componentSupport_prefixTriangles_finite hsc q

/-- Prefix triangles and inverse pairs form the exact strongly bounded family
used by the algebraic fan expansion. -/
def prefixCellRelations
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) :
    StronglyBoundedIdentityRelations
      (D.prefixQuotient W hsc.toIsSmallCancellation q hq) where
  relators := RelWord.prefixPresentationCells W q
  lengthBound := 3
  admissible := fun _word hword =>
    RelWord.admissible_of_mem_prefixPresentationCells
      hsc.toIsSmallCancellation q hq hword
  value_one := fun _word hword =>
    RelWord.listVal_eq_one_of_mem_prefixPresentationCells hword
  length_le := fun _word hword =>
    RelWord.length_le_three_of_mem_prefixPresentationCells hword
  componentSupport_finite :=
    RelWord.componentSupport_prefixPresentationCells_finite hsc q

namespace StronglyBoundedIdentityRelations

@[simp] theorem prefixCellRelations_lengthBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) :
    (prefixCellRelations D W hsc q hq).lengthBound = 3 := rfl

end StronglyBoundedIdentityRelations

end HullSC
end GroupApproximation
