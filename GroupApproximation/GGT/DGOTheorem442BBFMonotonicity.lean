import GroupApproximation.GGT.DGOTheorem442ProjectionMonotone

/-!
# Monotonicity of the BBF projection perturbation

This file proves property (F) of Bestvina--Bromberg--Fujiwara's projection
complex theorem.  If the modified projection of `(X,Z)` at `Y` is larger than
`4ξ`, then every admissible pair for `(X,Z)` is also admissible for `(X,Y)`;
after swapping its entries it is admissible for `(Z,Y)`.  Taking infima gives

`d_W(X,Y) ≤ d_W(X,Z)` and `d_W(Z,Y) ≤ d_W(X,Z)`

whenever all displayed projection distances are off the diagonal.
-/

namespace GroupApproximation
namespace GGT
namespace ProjectionSystem

universe u

variable {V : Type u}

/-- An admissible pair for `(X,Z)` whose projection at `Y` is larger than
`2ξ` is admissible for `(X,Y)`.  This is the set inclusion at the start of
BBF Theorem 3.3(F). -/
theorem bbfAdmissible_left_of_candidate_large
    (P : ProjectionSystem V) {Y X Z a b : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z)
    (hab : (a, b) ∈ P.bbfAdmissible X Z)
    (hYa : Y ≠ a) (hYb : Y ≠ b)
    (hlarge : 2 * P.ξ < P.projDist Y a b) :
    (a, b) ∈ P.bbfAdmissible X Y := by
  rcases hab with ⟨habne, hgeneral | hleft | hright | horiginal⟩
  · rcases hgeneral with ⟨hXa, hXb, _hZa, _hZb, hXab, _hZab⟩
    exact ⟨habne, Or.inl ⟨hXa, hXb, hYa, hYb, hXab, hlarge⟩⟩
  · rcases hleft with ⟨haX, _hZX, _hZb, _hZXb⟩
    exact ⟨habne, Or.inr (Or.inl ⟨haX, hYX, hYb, hlarge⟩)⟩
  · rcases hright with ⟨hbZ, hXa, hXZ, hXaZ⟩
    subst b
    exact ⟨habne, Or.inl ⟨hXa, hXZ, hYa, hYZ, hXaZ, hlarge⟩⟩
  · injection horiginal with ha hb
    subst a
    subst b
    exact ⟨habne, Or.inr (Or.inl ⟨rfl, hYX, hYZ, hlarge⟩)⟩

/-- A positive modified projection rules out BBF's exceptional zero case, so
the projection vertex is different from both entries of every admissible
pair. -/
theorem ne_entries_of_bbfProjDist_pos
    (P : ProjectionSystem V) {Y X Z a b : V}
    (hpos : 0 < P.bbfProjDist Y X Z)
    (hab : (a, b) ∈ P.bbfAdmissible X Z) :
    Y ≠ a ∧ Y ≠ b := by
  constructor
  · intro hYa
    have hcontains : (P.bbfContainingPairs Y X Z).Nonempty :=
      ⟨(a, b), hab, Or.inl hYa⟩
    rw [bbfProjDist, bbfRawProjDist,
      if_pos (Or.inr (Or.inr (Or.inr hcontains)))] at hpos
    exact lt_irrefl 0 hpos
  · intro hYb
    have hcontains : (P.bbfContainingPairs Y X Z).Nonempty :=
      ⟨(a, b), hab, Or.inr hYb⟩
    rw [bbfProjDist, bbfRawProjDist,
      if_pos (Or.inr (Or.inr (Or.inr hcontains)))] at hpos
    exact lt_irrefl 0 hpos

/-- If `d_Y(X,Z) > 4ξ`, every admissible pair for `(X,Z)` is admissible
for `(X,Y)`.  Proposition 2.2 first makes its `Y`-projection larger than
`2ξ`, and the preceding set-theoretic lemma applies. -/
theorem bbfAdmissible_left_of_large
    (P : ProjectionSystem V) {Y X Z a b : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hlarge : 4 * P.ξ < P.bbfProjDist Y X Z)
    (hab : (a, b) ∈ P.bbfAdmissible X Z) :
    (a, b) ∈ P.bbfAdmissible X Y := by
  have hpos : 0 < P.bbfProjDist Y X Z := by
    linarith [P.ξ_pos]
  obtain ⟨hYa, hYb⟩ := P.ne_entries_of_bbfProjDist_pos hpos hab
  have hclose := P.projDist_sub_candidate_lt_two_mul hYX hYZ hYa hYb hab
  have horiginal := P.bbfProjDist_le hYX hYZ hXZ
  have hcandidate : 2 * P.ξ < P.projDist Y a b := by linarith
  exact P.bbfAdmissible_left_of_candidate_large
    hYX hYZ hab hYa hYb hcandidate

/-- The corresponding admissible pair for `(Z,Y)` is obtained by reversing
the two entries. -/
theorem bbfAdmissible_right_of_large
    (P : ProjectionSystem V) {Y X Z a b : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hlarge : 4 * P.ξ < P.bbfProjDist Y X Z)
    (hab : (a, b) ∈ P.bbfAdmissible X Z) :
    (b, a) ∈ P.bbfAdmissible Z Y := by
  have hab' : (b, a) ∈ P.bbfAdmissible Z X :=
    (P.bbfAdmissible_swap_iff X Z a b).mp hab
  have hlarge' : 4 * P.ξ < P.bbfProjDist Y Z X := by
    rwa [P.bbfProjDist_comm]
  exact P.bbfAdmissible_left_of_large hYZ hYX hXZ.symm hlarge' hab'

/-- The numerical candidates for `d_W(X,Z)` form a subset of those for
`d_W(X,Y)` once the projection at `Y` is larger than `4ξ`. -/
theorem bbfCandidateValues_subset_left_of_large
    (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hlarge : 4 * P.ξ < P.bbfProjDist Y X Z) (W : V) :
    P.bbfCandidateValues W X Z ⊆ P.bbfCandidateValues W X Y := by
  rintro d ⟨⟨a, b⟩, hab, rfl⟩
  have hab' := P.bbfAdmissible_left_of_large
    hYX hYZ hXZ hlarge hab.1
  exact ⟨(a, b), ⟨hab', hab.2.1, hab.2.2⟩, rfl⟩

/-- BBF monotonicity, first inequality.  The endpoint hypotheses say that
both modified distances in the conclusion are in their published domains. -/
theorem bbfProjDist_left_mono
    (P : ProjectionSystem V) {W Y X Z : V}
    (hWX : W ≠ X) (hWY : W ≠ Y) (hWZ : W ≠ Z)
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hlarge : 4 * P.ξ < P.bbfProjDist Y X Z) :
    P.bbfProjDist W X Y ≤ P.bbfProjDist W X Z := by
  have hsubset := P.bbfCandidateValues_subset_left_of_large
    hYX hYZ hXZ hlarge W
  let targetZero : Prop := W = X ∨ W = Y ∨ X = Y ∨
    (P.bbfContainingPairs W X Y).Nonempty
  let sourceZero : Prop := W = X ∨ W = Z ∨ X = Z ∨
    (P.bbfContainingPairs W X Z).Nonempty
  by_cases htarget : targetZero
  · calc
      P.bbfProjDist W X Y = 0 := by
        rw [bbfProjDist, bbfRawProjDist, if_pos htarget]
      _ ≤ P.bbfProjDist W X Z := P.bbfProjDist_nonneg W X Z
  · by_cases hsource : sourceZero
    · exfalso
      apply htarget
      rcases hsource with hWX' | hWZ' | hXZ' | hcontains
      · exact Or.inl hWX'
      · exact (hWZ hWZ').elim
      · exact (hXZ hXZ').elim
      · right; right; right
        obtain ⟨⟨a, b⟩, hab, hW⟩ := hcontains
        exact ⟨(a, b),
          P.bbfAdmissible_left_of_large hYX hYZ hXZ hlarge hab, hW⟩
    · rw [bbfProjDist, bbfRawProjDist, if_neg htarget, if_neg hsource]
      exact csInf_le_csInf (P.bbfCandidateValues_bddBelow W X Y)
        (P.bbfCandidateValues_nonempty hWX hWZ hXZ) hsubset

/-- BBF monotonicity, second inequality.  It is the first inequality after
reversing `(X,Z)` and using symmetry of the modified distances. -/
theorem bbfProjDist_right_mono
    (P : ProjectionSystem V) {W Y X Z : V}
    (hWX : W ≠ X) (hWY : W ≠ Y) (hWZ : W ≠ Z)
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hlarge : 4 * P.ξ < P.bbfProjDist Y X Z) :
    P.bbfProjDist W Z Y ≤ P.bbfProjDist W X Z := by
  have hlarge' : 4 * P.ξ < P.bbfProjDist Y Z X := by
    rwa [P.bbfProjDist_comm]
  have hmono := P.bbfProjDist_left_mono hWZ hWY hWX
    hYZ hYX hXZ.symm hlarge'
  rwa [P.bbfProjDist_comm W Z X] at hmono

end ProjectionSystem
end GGT
end GroupApproximation
