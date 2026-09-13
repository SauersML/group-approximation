import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.GGT.HullSCLemma44RelativeDehn
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: the stretch bound

Ruling (A) leaves an unbound dart `d` of a cell `i` whose reverse also lies on `i` without a
competitor.  The cell word across the pocket between `d` and its reverse has value one, so the
route that skips the pocket spells the same element.  The cell word is `(λ, c)`-quasi-geodesic,
so the stretch is short.

This module proves the word half.
* A stretch `i, …, j` of a `(λ, c)`-quasi-geodesic word that spells the same element as an
  admissible word `alt` satisfies `λ (j - i) - c ≤ |alt|`.  With `j - i = X + |alt|` this is
  `λ X ≤ (1 - λ) |alt| + c`.
* If the stretch splits into blocks and every dropped block has value one, the kept letters
  are such a word `alt`.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.WordMetric

universe u w

section Stretch

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ}

/-- **The letters between two vertices spell the element between them.** -/
theorem vertex_one_inv_mul_vertex_one (word : List (RelLetter G Lambda)) {i j : ℕ}
    (hij : i ≤ j) :
    (OsinComponents.vertex 1 word i)⁻¹ * OsinComponents.vertex 1 word j =
      RelLetter.listVal ((word.drop i).take (j - i)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [OsinComponents.vertex_eq_mul_listVal_take word 1 i,
    OsinComponents.vertex_eq_mul_listVal_take word 1 (i + k), List.take_add,
    OsinComponents.listVal_append, Nat.add_sub_cancel_left, one_mul, one_mul,
    inv_mul_cancel_left]

/-- **A stretch of a quasi-geodesic word is not much longer than any respelling.** -/
theorem IsLambdaCQuasiGeodesicWord.stretch_le_length
    {word : List (RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ word.length) {alt : List (RelLetter G Lambda)}
    (halt : HullSC.RelWord.IsAdmissible D alt)
    (hval : RelLetter.listVal ((word.drop i).take (j - i)) = RelLetter.listVal alt) :
    lambda * ((j - i : ℕ) : ℝ) - c ≤ (alt.length : ℝ) := by
  have hquasi := hword.2 i j hij hj
  have hdist : wordDist D.alphabet.carrier (OsinComponents.vertex 1 word i)
      (OsinComponents.vertex 1 word j) ≤ alt.length := by
    unfold wordDist
    rw [vertex_one_inv_mul_vertex_one word hij, hval]
    exact HullSC.RelativeBoundaryContiguity.wordNorm_listVal_le_length D alt halt
  have hcast : ((wordDist D.alphabet.carrier (OsinComponents.vertex 1 word i)
      (OsinComponents.vertex 1 word j) : ℕ) : ℝ) ≤ (alt.length : ℝ) := by
    exact_mod_cast hdist
  linarith

/-- **The excursion form.**  If the stretch is `X` letters more than `alt`, then
`λ X ≤ (1 - λ) |alt| + c`. -/
theorem IsLambdaCQuasiGeodesicWord.excursion_le
    {word : List (RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ word.length) {alt : List (RelLetter G Lambda)}
    (halt : HullSC.RelWord.IsAdmissible D alt)
    (hval : RelLetter.listVal ((word.drop i).take (j - i)) = RelLetter.listVal alt)
    {X : ℕ} (hlen : j - i = X + alt.length) :
    lambda * (X : ℝ) ≤ (1 - lambda) * (alt.length : ℝ) + c := by
  have h := hword.stretch_le_length hij hj halt hval
  rw [hlen, Nat.cast_add] at h
  linarith

end Stretch

section Pieces

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ}

/-- The letters of the kept blocks of a block decomposition.  The dropped blocks are the
closed pocket intervals, whose words have value one. -/
def keptLetters (pieces : List (List (RelLetter G Lambda) × Bool)) :
    List (RelLetter G Lambda) :=
  (pieces.filter fun p => p.2).flatMap Prod.fst

/-- **Dropping value-one blocks does not change the value.** -/
theorem listVal_flatMap_eq_listVal_keptLetters
    (pieces : List (List (RelLetter G Lambda) × Bool))
    (hone : ∀ p ∈ pieces, p.2 = false → RelLetter.listVal p.1 = 1) :
    RelLetter.listVal (pieces.flatMap Prod.fst) = RelLetter.listVal (keptLetters pieces) := by
  induction pieces with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨v, b⟩ := p
      have ih' := ih fun q hq => hone q (List.mem_cons_of_mem _ hq)
      cases b
      · have hv : RelLetter.listVal v = 1 := hone (v, false) List.mem_cons_self rfl
        rw [List.flatMap_cons, OsinComponents.listVal_append, hv, one_mul, ih']
        simp [keptLetters]
      · rw [List.flatMap_cons, OsinComponents.listVal_append, ih']
        simp [keptLetters, List.flatMap_cons, OsinComponents.listVal_append]

/-- **A stretch whose value-one blocks are dropped.**  If the stretch `i, …, j` splits into
blocks and every dropped block has value one, the stretch is not much longer than its kept
letters. -/
theorem IsLambdaCQuasiGeodesicWord.stretch_le_keptLetters
    {word : List (RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ word.length)
    (pieces : List (List (RelLetter G Lambda) × Bool))
    (hsplit : (word.drop i).take (j - i) = pieces.flatMap Prod.fst)
    (hone : ∀ p ∈ pieces, p.2 = false → RelLetter.listVal p.1 = 1) :
    lambda * ((j - i : ℕ) : ℝ) - c ≤ ((keptLetters pieces).length : ℝ) := by
  refine hword.stretch_le_length hij hj ?_ ?_
  · intro a ha
    obtain ⟨p, hp, hap⟩ := List.mem_flatMap.mp ha
    have hmem : a ∈ pieces.flatMap Prod.fst :=
      List.mem_flatMap.mpr ⟨p, (List.mem_filter.mp hp).1, hap⟩
    rw [← hsplit] at hmem
    exact hword.1 a (List.mem_of_mem_drop (List.mem_of_mem_take hmem))
  · rw [hsplit]
    exact listVal_flatMap_eq_listVal_keptLetters pieces hone

end Pieces

/-- **Printed endpoint.**  A stretch of a `(λ, c)`-quasi-geodesic word that spells the same
element as an admissible word `alt` exceeds `alt` by at most `((1 - λ) |alt| + c) / λ` letters. -/
def OsinUnboundSameCellStretchBound : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ)
    (word : List (RelLetter G Lambda)), IsLambdaCQuasiGeodesicWord D lambda c word →
    ∀ i j : ℕ, i ≤ j → j ≤ word.length →
      ∀ (alt : List (RelLetter G Lambda)), HullSC.RelWord.IsAdmissible D alt →
        RelLetter.listVal ((word.drop i).take (j - i)) = RelLetter.listVal alt →
        ∀ X : ℕ, j - i = X + alt.length →
          lambda * (X : ℝ) ≤ (1 - lambda) * (alt.length : ℝ) + c

theorem osinUnboundSameCellStretchBound_holds :
    OsinUnboundSameCellStretchBound.{u, w} := by
  intro G _ Lambda D lambda c word hword i j hij hj alt halt hval X hlen
  exact hword.excursion_le hij hj halt hval hlen

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinUnboundSameCellStretchBound_holds
#audit_axioms GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.stretch_le_keptLetters
