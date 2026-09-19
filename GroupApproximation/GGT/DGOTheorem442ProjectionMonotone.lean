import GroupApproximation.GGT.DGOTheorem442ProjectionSystem

/-!
# The monotone BBF perturbation used in DGO Theorem 4.42

The projection complex is not built from the original projection distances.
Bestvina--Bromberg--Fujiwara first replace them by an infimum over their
admissible pairs.  This file formalizes that actual construction, beginning
with Proposition 2.2 of their projection-complex paper: every admissible value
is less than `2ξ` below the original value.  In particular the infimum is a
genuine `2ξ` perturbation, rather than the identity substitute.
-/

namespace GroupApproximation
namespace GGT

universe u

namespace ProjectionSystem

variable {V : Type u}

/-- BBF's set `H(X,Z)` of pairs over which the monotone projection distance is
defined.  The inequalities are written with the strict orientation used in
the source. -/
def bbfAdmissible (P : ProjectionSystem V) (X Z : V) : Set (V × V) :=
  {p | p.1 ≠ p.2 ∧
      ((X ≠ p.1 ∧ X ≠ p.2 ∧ Z ≠ p.1 ∧ Z ≠ p.2 ∧
          2 * P.ξ < P.projDist X p.1 p.2 ∧
          2 * P.ξ < P.projDist Z p.1 p.2) ∨
        (p.1 = X ∧ Z ≠ X ∧ Z ≠ p.2 ∧
          2 * P.ξ < P.projDist Z X p.2) ∨
        (p.2 = Z ∧ X ≠ p.1 ∧ X ≠ Z ∧
          2 * P.ξ < P.projDist X p.1 Z) ∨
        p = (X, Z))}

/-- The original pair belongs to `H(X,Z)`. -/
theorem pair_mem_bbfAdmissible (P : ProjectionSystem V) {X Z : V}
    (hXZ : X ≠ Z) :
    (X, Z) ∈ P.bbfAdmissible X Z :=
  ⟨hXZ, Or.inr (Or.inr (Or.inr rfl))⟩

/-- Swapping both endpoints and both entries preserves BBF admissibility. -/
theorem bbfAdmissible_swap_iff (P : ProjectionSystem V)
    (X Z a b : V) :
    (a, b) ∈ P.bbfAdmissible X Z ↔
      (b, a) ∈ P.bbfAdmissible Z X := by
  have hswap : ∀ {X Z a b : V},
      (a, b) ∈ P.bbfAdmissible X Z →
        (b, a) ∈ P.bbfAdmissible Z X := by
    intro X Z a b h
    rcases h with ⟨hab, hgeneral | hleft | hright | horiginal⟩
    · rcases hgeneral with ⟨hXa, hXb, hZa, hZb, hXab, hZab⟩
      refine ⟨hab.symm, Or.inl ⟨hZb, hZa, hXb, hXa, ?_, ?_⟩⟩
      · rwa [P.comm]
      · rwa [P.comm]
    · rcases hleft with ⟨haX, hZX, hZb, hdist⟩
      refine ⟨hab.symm, Or.inr (Or.inr (Or.inl ⟨haX, hZb, hZX, ?_⟩))⟩
      rwa [P.comm]
    · rcases hright with ⟨hbZ, hXa, hXZ, hdist⟩
      refine ⟨hab.symm, Or.inr (Or.inl ⟨hbZ, hXZ, hXa, ?_⟩)⟩
      rwa [P.comm]
    · refine ⟨hab.symm, ?_⟩
      right; right; right
      injection horiginal with ha hb
      subst a
      subst b
      rfl
  exact ⟨hswap, hswap⟩

/-- Candidates for the projection at `Y` must avoid `Y`, exactly as in the
domain `(𝒴 \ {Y})²` of the published projection distances. -/
def bbfCandidatePairs (P : ProjectionSystem V) (Y X Z : V) : Set (V × V) :=
  {p | p ∈ P.bbfAdmissible X Z ∧ Y ≠ p.1 ∧ Y ≠ p.2}

theorem pair_mem_bbfCandidatePairs (P : ProjectionSystem V)
    {Y X Z : V} (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    (X, Z) ∈ P.bbfCandidatePairs Y X Z :=
  ⟨P.pair_mem_bbfAdmissible hXZ, hYX, hYZ⟩

/-- The set of numerical values whose infimum is the modified distance. -/
def bbfCandidateValues (P : ProjectionSystem V) (Y X Z : V) : Set ℝ :=
  (fun p : V × V => P.projDist Y p.1 p.2) ''
    P.bbfCandidatePairs Y X Z

theorem bbfCandidateValues_nonempty (P : ProjectionSystem V)
    {Y X Z : V} (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    (P.bbfCandidateValues Y X Z).Nonempty :=
  ⟨P.projDist Y X Z,
    ⟨(X, Z), P.pair_mem_bbfCandidatePairs hYX hYZ hXZ, rfl⟩⟩

theorem bbfCandidateValues_bddBelow (P : ProjectionSystem V)
    (Y X Z : V) : BddBelow (P.bbfCandidateValues Y X Z) := by
  refine ⟨0, ?_⟩
  rintro d ⟨p, -, rfl⟩
  exact P.nonneg Y p.1 p.2

/-- The candidate-value set is symmetric in the two projected endpoints. -/
theorem bbfCandidateValues_comm (P : ProjectionSystem V) (Y X Z : V) :
    P.bbfCandidateValues Y X Z = P.bbfCandidateValues Y Z X := by
  ext d
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(p.2, p.1), ⟨?_, hp.2.2, hp.2.1⟩, ?_⟩
    · exact (P.bbfAdmissible_swap_iff X Z p.1 p.2).mp hp.1
    · exact P.comm Y p.2 p.1
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(p.2, p.1), ⟨?_, hp.2.2, hp.2.1⟩, ?_⟩
    · exact (P.bbfAdmissible_swap_iff Z X p.1 p.2).mp hp.1
    · exact P.comm Y p.2 p.1

/-- The admissible pairs for `(X,Z)` which contain the projection vertex `Y`.
The modified distance is zero when this set is nonempty. -/
def bbfContainingPairs (P : ProjectionSystem V) (Y X Z : V) : Set (V × V) :=
  {p | p ∈ P.bbfAdmissible X Z ∧ (Y = p.1 ∨ Y = p.2)}

/-- Simultaneously reversing the endpoints and the admissible pair preserves
the exceptional zero case. -/
theorem bbfContainingPairs_nonempty_comm (P : ProjectionSystem V) (Y X Z : V) :
    (P.bbfContainingPairs Y X Z).Nonempty ↔
      (P.bbfContainingPairs Y Z X).Nonempty := by
  constructor
  · rintro ⟨p, hp, hY⟩
    refine ⟨(p.2, p.1), (P.bbfAdmissible_swap_iff X Z p.1 p.2).mp hp, ?_⟩
    exact hY.elim Or.inr Or.inl
  · rintro ⟨p, hp, hY⟩
    refine ⟨(p.2, p.1), (P.bbfAdmissible_swap_iff Z X p.1 p.2).mp hp, ?_⟩
    exact hY.elim Or.inr Or.inl

/-- If `Y` occurs in an admissible pair for `(X,Z)`, the original projection
at `Y` is already below `2ξ`.  This is the PC2--PC3 estimate immediately
before BBF Proposition 2.2 and justifies the exceptional value zero. -/
theorem projDist_lt_two_mul_of_bbfContains
    (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z)
    (hcontains : (P.bbfContainingPairs Y X Z).Nonempty) :
    P.projDist Y X Z < 2 * P.ξ := by
  obtain ⟨⟨a, b⟩, hab, hY⟩ := hcontains
  have hab' : a ≠ b ∧
      ((X ≠ a ∧ X ≠ b ∧ Z ≠ a ∧ Z ≠ b ∧
          2 * P.ξ < P.projDist X a b ∧
          2 * P.ξ < P.projDist Z a b) ∨
        (a = X ∧ Z ≠ X ∧ Z ≠ b ∧
          2 * P.ξ < P.projDist Z X b) ∨
        (b = Z ∧ X ≠ a ∧ X ≠ Z ∧
          2 * P.ξ < P.projDist X a Z) ∨
        (a, b) = (X, Z)) := by
    simpa only [bbfAdmissible, Set.mem_setOf_eq] using hab
  have hY' : Y = a ∨ Y = b := by
    simpa only using hY
  rcases hab' with ⟨habne, hgeneral | hleft | hright | horiginal⟩
  · rcases hgeneral with ⟨hXa, hXb, hZa, hZb, hXab, hZab⟩
    rcases hY' with hYa | hYb
    · subst a
      have hYXb : P.projDist Y X b < P.ξ := by
        have hmin := P.behrstock X b Y hXb hYX.symm habne.symm
        have hlarge : P.ξ < P.projDist X b Y := by
          rw [P.comm]
          linarith [P.ξ_pos]
        have hsmall := (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hlarge))
        rwa [P.comm] at hsmall
      have hYbZ : P.projDist Y b Z < P.ξ := by
        have hmin := P.behrstock Z b Y hZb hYZ.symm habne.symm
        have hlarge : P.ξ < P.projDist Z b Y := by
          rw [P.comm]
          linarith [P.ξ_pos]
        exact (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hlarge))
      have htri := P.triangle Y X b Z hYX habne hYZ
      linarith
    · subst b
      have hYXa : P.projDist Y X a < P.ξ := by
        have hmin := P.behrstock X a Y hXa hYX.symm habne
        have hlarge : P.ξ < P.projDist X a Y := by
          linarith [P.ξ_pos]
        have hsmall := (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hlarge))
        rwa [P.comm] at hsmall
      have hYaZ : P.projDist Y a Z < P.ξ := by
        have hmin := P.behrstock Z a Y hZa hYZ.symm habne
        have hlarge : P.ξ < P.projDist Z a Y := by
          linarith [P.ξ_pos]
        exact (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hlarge))
      have htri := P.triangle Y X a Z hYX habne.symm hYZ
      linarith
  · rcases hleft with ⟨haX, hZX, hZb, hZXb⟩
    subst a
    rcases hY' with hYX' | hYb
    · exact (hYX hYX').elim
    · subst b
      have hmin := P.behrstock Z X Y hZX hYZ.symm habne
      have hlarge : P.ξ < P.projDist Z X Y := by linarith [P.ξ_pos]
      have hsmall := (min_lt_iff.mp hmin).resolve_left
        (not_lt_of_ge (le_of_lt hlarge))
      exact hsmall.trans_le (by linarith [P.ξ_pos])
  · rcases hright with ⟨hbZ, hXa, hXZ, hXaZ⟩
    subst b
    rcases hY' with hYa | hYZ'
    · subst a
      have hmin := P.behrstock X Z Y hXZ hYX.symm habne.symm
      have hlarge : P.ξ < P.projDist X Z Y := by
        rw [P.comm]
        linarith [P.ξ_pos]
      have hsmall := (min_lt_iff.mp hmin).resolve_left
        (not_lt_of_ge (le_of_lt hlarge))
      rw [P.comm] at hsmall
      exact hsmall.trans_le (by linarith [P.ξ_pos])
    · exact (hYZ hYZ').elim
  · cases horiginal
    rcases hY' with hYX' | hYZ'
    · exact (hYX hYX').elim
    · exact (hYZ hYZ').elim
/-- The raw BBF infimum.  Projection distances are used only off the
diagonal; assigning zero on the excluded diagonal makes the totalized Lean
function nonnegative without changing any published value. -/
noncomputable def bbfRawProjDist (P : ProjectionSystem V) (Y X Z : V) : ℝ :=
  by
    classical
    exact if Y = X ∨ Y = Z ∨ X = Z ∨
        (P.bbfContainingPairs Y X Z).Nonempty then 0
      else sInf (P.bbfCandidateValues Y X Z)

theorem bbfRawProjDist_nonneg (P : ProjectionSystem V) (Y X Z : V) :
    0 ≤ P.bbfRawProjDist Y X Z := by
  classical
  rw [bbfRawProjDist]
  split_ifs with h
  · exact le_rfl
  · push Not at h
    exact le_csInf (P.bbfCandidateValues_nonempty h.1 h.2.1 h.2.2.1) (by
      rintro d ⟨p, -, rfl⟩
      exact P.nonneg Y p.1 p.2)

/-- The modified distance is at most the original one. -/
theorem bbfRawProjDist_le (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    P.bbfRawProjDist Y X Z ≤ P.projDist Y X Z := by
  classical
  rw [bbfRawProjDist]
  split_ifs with h
  · exact P.nonneg Y X Z
  · exact csInf_le (P.bbfCandidateValues_bddBelow Y X Z)
      ⟨(X, Z), P.pair_mem_bbfCandidatePairs hYX hYZ hXZ, rfl⟩

/-- The raw BBF infimum is already symmetric; no post-hoc symmetrization is
needed. -/
theorem bbfRawProjDist_comm (P : ProjectionSystem V) (Y X Z : V) :
    P.bbfRawProjDist Y X Z = P.bbfRawProjDist Y Z X := by
  classical
  rw [bbfRawProjDist, bbfRawProjDist]
  have hor : Y = X ∨ Y = Z ∨ X = Z ∨
        (P.bbfContainingPairs Y X Z).Nonempty ↔
      Y = Z ∨ Y = X ∨ Z = X ∨
        (P.bbfContainingPairs Y Z X).Nonempty := by
    rw [P.bbfContainingPairs_nonempty_comm]
    aesop
  rw [if_congr hor rfl rfl]
  split_ifs
  · rfl
  · rw [P.bbfCandidateValues_comm]

/-- Every admissible candidate lies less than `2ξ` below the original
projection value (BBF Proposition 2.2). -/
theorem projDist_sub_candidate_lt_two_mul
    (P : ProjectionSystem V) {Y X Z a b : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z)
    (haY : Y ≠ a) (hbY : Y ≠ b)
    (hab : (a, b) ∈ P.bbfAdmissible X Z) :
    P.projDist Y X Z - P.projDist Y a b < 2 * P.ξ := by
  simp only [bbfAdmissible, Set.mem_setOf_eq] at hab
  by_cases hsmall : P.projDist Y X Z < 2 * P.ξ
  · linarith [P.nonneg Y a b]
  have hbig : 2 * P.ξ ≤ P.projDist Y X Z := le_of_not_gt hsmall
  have hbigξ : P.ξ < P.projDist Y X Z := by linarith [P.ξ_pos]
  rcases hab with ⟨_habne, hgeneral | hleft | hright | horiginal⟩
  · rcases hgeneral with ⟨hXa, hXb, hZa, hZb, hXab, hZab⟩
    have htriX := P.triangle X a Y b hXa hYX.symm hXb
    have hsplit : P.ξ < P.projDist X a Y ∨ P.ξ < P.projDist X Y b := by
      by_contra h
      push Not at h
      linarith
    have hcase : ∀ {a' b' : V},
        X ≠ a' → X ≠ b' → Z ≠ a' → Z ≠ b' →
        Y ≠ a' → Y ≠ b' →
        2 * P.ξ < P.projDist Z a' b' →
        P.ξ < P.projDist X a' Y →
        P.projDist Y X Z - P.projDist Y a' b' < 2 * P.ξ := by
      intro a' b' hXa' hXb' hZa' hZb' hYa' hYb' hZa'b' hXa'Y
      have hYa'X : P.projDist Y a' X < P.ξ := by
        have hmin := P.behrstock X a' Y hXa' hYX.symm hYa'.symm
        exact (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hXa'Y))
      have hYXa' : P.projDist Y X a' < P.ξ := by
        rw [P.comm]
        exact hYa'X
      have htriY₁ := P.triangle Y X a' Z hYX hYa' hYZ
      have hYa'Z : P.ξ < P.projDist Y a' Z := by linarith
      have hZa'Y : P.projDist Z a' Y < P.ξ := by
        have hmin := P.behrstock Y a' Z hYa' hYZ hZa'.symm
        exact (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hYa'Z))
      have hZYb' : P.ξ < P.projDist Z Y b' := by
        have htriZ := P.triangle Z a' Y b' hZa' hYZ.symm hZb'
        linarith
      have hYb'Z : P.projDist Y b' Z < P.ξ := by
        have hmin := P.behrstock Z b' Y hZb' hYZ.symm hYb'.symm
        have hZb'Y : P.ξ < P.projDist Z b' Y := by rwa [P.comm]
        exact (min_lt_iff.mp hmin).resolve_left
          (not_lt_of_ge (le_of_lt hZb'Y))
      have htriY₂ := P.triangle Y a' b' Z hYa' hYb' hYZ
      linarith
    rcases hsplit with hXaY | hXYb
    · exact hcase hXa hXb hZa hZb haY hbY hZab hXaY
    · have hXbY : P.ξ < P.projDist X b Y := by rwa [P.comm]
      have hZba : 2 * P.ξ < P.projDist Z b a := by rwa [P.comm]
      have hswap := hcase hXb hXa hZb hZa hbY haY hZba hXbY
      rwa [P.comm Y b a] at hswap
  · rcases hleft with ⟨haX, hZX, hZb, hZXb⟩
    subst a
    have hZXY : P.projDist Z X Y < P.ξ := by
      have hmin := P.behrstock Y X Z hYX hYZ hZX.symm
      exact (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge (le_of_lt hbigξ))
    have hZYb : P.ξ < P.projDist Z Y b := by
      have htriZ := P.triangle Z X Y b hZX hYZ.symm hZb
      linarith
    have hYbZ : P.projDist Y b Z < P.ξ := by
      have hmin := P.behrstock Z b Y hZb hYZ.symm hbY.symm
      have hZbY : P.ξ < P.projDist Z b Y := by rwa [P.comm]
      exact (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge (le_of_lt hZbY))
    have htriY := P.triangle Y X b Z hYX hbY hYZ
    linarith [P.ξ_pos]
  · rcases hright with ⟨hbZ, hXa, hXZ, hXaZ⟩
    subst b
    have hXYZ : P.projDist X Y Z < P.ξ := by
      have hmin := P.behrstock Y Z X hYZ hYX hXZ.symm
      have hYXZ : P.ξ < P.projDist Y Z X := by rwa [P.comm]
      have hXZY := (min_lt_iff.mp hmin).resolve_left
        (not_lt_of_ge (le_of_lt hYXZ))
      rwa [P.comm] at hXZY
    have hXaY : P.ξ < P.projDist X a Y := by
      have htriX := P.triangle X a Y Z hXa hYX.symm hXZ
      linarith
    have hYaX : P.projDist Y a X < P.ξ := by
      have hmin := P.behrstock X a Y hXa hYX.symm haY.symm
      exact (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge (le_of_lt hXaY))
    have hYXa : P.projDist Y X a < P.ξ := by rw [P.comm]; exact hYaX
    have htriY := P.triangle Y X a Z hYX haY hYZ
    linarith [P.ξ_pos]
  · cases horiginal
    linarith [P.ξ_pos]

/-- The raw infimum is at most `2ξ` below the original distance.  Proposition
2.2 gives a strict inequality for every candidate.  Passing to an infimum
retains exactly the non-strict bound used by the perturbation structure. -/
theorem projDist_sub_bbfRawProjDist_le_two_mul
    (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    P.projDist Y X Z - P.bbfRawProjDist Y X Z ≤ 2 * P.ξ := by
  classical
  rw [bbfRawProjDist]
  split_ifs with hzero
  · have hcontains : (P.bbfContainingPairs Y X Z).Nonempty := by
      rcases hzero with hYX' | hYZ' | hXZ' | hcontains
      · exact (hYX hYX').elim
      · exact (hYZ hYZ').elim
      · exact (hXZ hXZ').elim
      · exact hcontains
    have hsmall := P.projDist_lt_two_mul_of_bbfContains hYX hYZ hcontains
    linarith
  · have hle : P.projDist Y X Z - 2 * P.ξ ≤
        sInf (P.bbfCandidateValues Y X Z) := by
      apply le_csInf (P.bbfCandidateValues_nonempty hYX hYZ hXZ)
      rintro d ⟨p, hp, rfl⟩
      have hcandidate :=
        P.projDist_sub_candidate_lt_two_mul hYX hYZ hp.2.1 hp.2.2 hp.1
      linarith
    linarith

/-- The published modified distance is the raw admissible-pair infimum. -/
noncomputable def bbfProjDist (P : ProjectionSystem V) (Y X Z : V) : ℝ :=
  P.bbfRawProjDist Y X Z

theorem bbfProjDist_nonneg (P : ProjectionSystem V) (Y X Z : V) :
    0 ≤ P.bbfProjDist Y X Z :=
  P.bbfRawProjDist_nonneg Y X Z

theorem bbfProjDist_comm (P : ProjectionSystem V) (Y X Z : V) :
    P.bbfProjDist Y X Z = P.bbfProjDist Y Z X := by
  exact P.bbfRawProjDist_comm Y X Z

theorem bbfProjDist_le (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    P.bbfProjDist Y X Z ≤ P.projDist Y X Z :=
  P.bbfRawProjDist_le hYX hYZ hXZ

theorem projDist_sub_bbfProjDist_le_two_mul
    (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z) :
    P.projDist Y X Z - P.bbfProjDist Y X Z ≤ 2 * P.ξ := by
  exact P.projDist_sub_bbfRawProjDist_le_two_mul hYX hYZ hXZ

/-- The strengthened Behrstock inequality for the modified distances: a
projection larger than `2ξ` forces both endpoint projections below `ξ`. -/
theorem bbfProjDist_endpoints_lt (P : ProjectionSystem V)
    {Y X Z : V} (hYX : Y ≠ X) (hYZ : Y ≠ Z) (hXZ : X ≠ Z)
    (hlarge : 2 * P.ξ < P.bbfProjDist Y X Z) :
    P.bbfProjDist X Y Z < P.ξ ∧ P.bbfProjDist Z X Y < P.ξ := by
  have horiginal : P.ξ < P.projDist Y X Z := by
    have hle := P.bbfProjDist_le hYX hYZ hXZ
    linarith [P.ξ_pos]
  have hX : P.projDist X Y Z < P.ξ := by
    have hmin := P.behrstock Y Z X hYZ hYX hXZ.symm
    rw [P.comm Y Z X] at hmin
    have hsmall :=
      (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge (le_of_lt horiginal))
    rwa [P.comm] at hsmall
  have hZ : P.projDist Z X Y < P.ξ := by
    have hmin := P.behrstock Y X Z hYX hYZ hXZ
    exact (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge (le_of_lt horiginal))
  exact ⟨
    (P.bbfProjDist_le hYX.symm hXZ hYZ).trans_lt hX,
    (P.bbfProjDist_le hXZ.symm hYZ.symm hYX.symm).trans_lt hZ⟩

end ProjectionSystem

namespace EquivariantProjectionSystem

universe v

variable {G : Type u} {V : Type v} [Group G] [MulAction G V]

/-- BBF admissibility is preserved by simultaneous translation. -/
theorem bbfAdmissible_smul_iff (P : EquivariantProjectionSystem G V)
    (g : G) (X Z a b : V) :
    (g • a, g • b) ∈ P.toProjectionSystem.bbfAdmissible (g • X) (g • Z) ↔
      (a, b) ∈ P.toProjectionSystem.bbfAdmissible X Z := by
  have heq : ∀ x y : V, g • x = g • y ↔ x = y := by
    intro x y
    constructor
    · exact smul_left_cancel g
    · rintro rfl
      rfl
  have hne : ∀ x y : V, g • x ≠ g • y ↔ x ≠ y := by
    intro x y
    exact not_congr (heq x y)
  simp only [ProjectionSystem.bbfAdmissible, Set.mem_setOf_eq,
    P.smul_projDist, heq, hne, Prod.mk.injEq]

/-- Simultaneous translation does not change the set of numerical candidates
whose infimum defines the raw BBF projection distance. -/
theorem bbfCandidateValues_smul (P : EquivariantProjectionSystem G V)
    (g : G) (Y X Z : V) :
    P.toProjectionSystem.bbfCandidateValues (g • Y) (g • X) (g • Z) =
      P.toProjectionSystem.bbfCandidateValues Y X Z := by
  ext d
  constructor
  · rintro ⟨p, hp, rfl⟩
    let a : V := g⁻¹ • p.1
    let b : V := g⁻¹ • p.2
    refine ⟨(a, b), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · apply (P.bbfAdmissible_smul_iff g X Z a b).mp
        simpa only [a, b, smul_inv_smul] using hp.1
      · intro hYa
        apply hp.2.1
        rw [hYa]
        simp only [a, smul_inv_smul]
      · intro hYb
        apply hp.2.2
        rw [hYb]
        simp only [b, smul_inv_smul]
    · have hdist := P.smul_projDist g Y a b
      simpa only [a, b, smul_inv_smul] using hdist.symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(g • p.1, g • p.2), ?_, ?_⟩
    · refine ⟨(P.bbfAdmissible_smul_iff g X Z p.1 p.2).mpr hp.1, ?_, ?_⟩
      · intro h
        exact hp.2.1 (smul_left_cancel g h)
      · intro h
        exact hp.2.2 (smul_left_cancel g h)
    · exact P.smul_projDist g Y p.1 p.2

/-- The exceptional zero case is preserved by simultaneous translation. -/
theorem bbfContainingPairs_nonempty_smul_iff
    (P : EquivariantProjectionSystem G V)
    (g : G) (Y X Z : V) :
    (P.toProjectionSystem.bbfContainingPairs (g • Y) (g • X) (g • Z)).Nonempty ↔
      (P.toProjectionSystem.bbfContainingPairs Y X Z).Nonempty := by
  constructor
  · rintro ⟨⟨a, b⟩, hab, hY⟩
    let a₀ : V := g⁻¹ • a
    let b₀ : V := g⁻¹ • b
    refine ⟨(a₀, b₀), ?_, ?_⟩
    · apply (P.bbfAdmissible_smul_iff g X Z a₀ b₀).mp
      simpa only [a₀, b₀, smul_inv_smul] using hab
    · rcases hY with hYa | hYb
      · left
        apply smul_left_cancel g
        simpa only [a₀, smul_inv_smul] using hYa
      · right
        apply smul_left_cancel g
        simpa only [b₀, smul_inv_smul] using hYb
  · rintro ⟨⟨a, b⟩, hab, hY⟩
    refine ⟨(g • a, g • b),
      (P.bbfAdmissible_smul_iff g X Z a b).mpr hab, ?_⟩
    rcases hY with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The raw BBF infimum is equivariant. -/
theorem bbfRawProjDist_smul (P : EquivariantProjectionSystem G V)
    (g : G) (Y X Z : V) :
    P.toProjectionSystem.bbfRawProjDist (g • Y) (g • X) (g • Z) =
      P.toProjectionSystem.bbfRawProjDist Y X Z := by
  classical
  rw [ProjectionSystem.bbfRawProjDist, ProjectionSystem.bbfRawProjDist]
  have hor : g • Y = g • X ∨ g • Y = g • Z ∨ g • X = g • Z ∨
        (P.toProjectionSystem.bbfContainingPairs
          (g • Y) (g • X) (g • Z)).Nonempty ↔
      Y = X ∨ Y = Z ∨ X = Z ∨
        (P.toProjectionSystem.bbfContainingPairs Y X Z).Nonempty := by
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (smul_left_cancel g h)
      · exact Or.inr (Or.inl (smul_left_cancel g h))
      · exact Or.inr (Or.inr (Or.inl (smul_left_cancel g h)))
      · exact Or.inr (Or.inr (Or.inr
          ((P.bbfContainingPairs_nonempty_smul_iff g Y X Z).mp h)))
    · rintro (rfl | rfl | rfl | h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr
          ((P.bbfContainingPairs_nonempty_smul_iff g Y X Z).mpr h)))
  rw [if_congr hor rfl rfl]
  split_ifs
  · rfl
  · rw [P.bbfCandidateValues_smul]

/-- The symmetric BBF perturbation is equivariant. -/
theorem bbfProjDist_smul (P : EquivariantProjectionSystem G V)
    (g : G) (Y X Z : V) :
    P.toProjectionSystem.bbfProjDist (g • Y) (g • X) (g • Z) =
      P.toProjectionSystem.bbfProjDist Y X Z := by
  simp only [ProjectionSystem.bbfProjDist, P.bbfRawProjDist_smul]

end EquivariantProjectionSystem
end GGT
end GroupApproximation
