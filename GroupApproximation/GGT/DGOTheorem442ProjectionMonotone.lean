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
  {p | (X ≠ p.1 ∧ X ≠ p.2 ∧ Z ≠ p.1 ∧ Z ≠ p.2 ∧
          2 * P.ξ < P.projDist X p.1 p.2 ∧
          2 * P.ξ < P.projDist Z p.1 p.2) ∨
        (p.1 = X ∧ Z ≠ X ∧ Z ≠ p.2 ∧
          2 * P.ξ < P.projDist Z X p.2) ∨
        (p.2 = Z ∧ X ≠ p.1 ∧ X ≠ Z ∧
          2 * P.ξ < P.projDist X p.1 Z) ∨
        p = (X, Z)}

/-- The original pair belongs to `H(X,Z)`. -/
theorem pair_mem_bbfAdmissible (P : ProjectionSystem V) (X Z : V) :
    (X, Z) ∈ P.bbfAdmissible X Z :=
  Or.inr (Or.inr (Or.inr rfl))

/-- Swapping both endpoints and both entries preserves BBF admissibility. -/
theorem bbfAdmissible_swap_iff (P : ProjectionSystem V)
    (X Z a b : V) :
    (a, b) ∈ P.bbfAdmissible X Z ↔
      (b, a) ∈ P.bbfAdmissible Z X := by
  have hswap : ∀ {X Z a b : V},
      (a, b) ∈ P.bbfAdmissible X Z →
        (b, a) ∈ P.bbfAdmissible Z X := by
    intro X Z a b h
    rcases h with hgeneral | hleft | hright | horiginal
    · rcases hgeneral with ⟨hXa, hXb, hZa, hZb, hXab, hZab⟩
      left
      refine ⟨hZb, hZa, hXb, hXa, ?_, ?_⟩
      · rwa [P.comm]
      · rwa [P.comm]
    · rcases hleft with ⟨haX, hZX, hZb, hdist⟩
      right; right; left
      refine ⟨haX, hZb, hZX, ?_⟩
      rwa [P.comm]
    · rcases hright with ⟨hbZ, hXa, hXZ, hdist⟩
      right; left
      refine ⟨hbZ, hXZ, hXa, ?_⟩
      rwa [P.comm]
    · right; right; right
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
    {Y X Z : V} (hYX : Y ≠ X) (hYZ : Y ≠ Z) :
    (X, Z) ∈ P.bbfCandidatePairs Y X Z :=
  ⟨P.pair_mem_bbfAdmissible X Z, hYX, hYZ⟩

/-- The set of numerical values whose infimum is the modified distance. -/
def bbfCandidateValues (P : ProjectionSystem V) (Y X Z : V) : Set ℝ :=
  (fun p : V × V => P.projDist Y p.1 p.2) ''
    P.bbfCandidatePairs Y X Z

theorem bbfCandidateValues_nonempty (P : ProjectionSystem V)
    {Y X Z : V} (hYX : Y ≠ X) (hYZ : Y ≠ Z) :
    (P.bbfCandidateValues Y X Z).Nonempty :=
  ⟨P.projDist Y X Z, ⟨(X, Z), P.pair_mem_bbfCandidatePairs hYX hYZ, rfl⟩⟩

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

/-- The raw BBF infimum.  Projection distances are used only off the
diagonal; assigning zero on the excluded diagonal makes the totalized Lean
function nonnegative without changing any published value. -/
noncomputable def bbfRawProjDist (P : ProjectionSystem V) (Y X Z : V) : ℝ :=
  by
    classical
    exact if Y = X ∨ Y = Z then 0 else sInf (P.bbfCandidateValues Y X Z)

theorem bbfRawProjDist_nonneg (P : ProjectionSystem V) (Y X Z : V) :
    0 ≤ P.bbfRawProjDist Y X Z := by
  classical
  rw [bbfRawProjDist]
  split_ifs with h
  · exact le_rfl
  · push Not at h
    exact le_csInf (P.bbfCandidateValues_nonempty h.1 h.2) (by
      rintro d ⟨p, -, rfl⟩
      exact P.nonneg Y p.1 p.2)

/-- The modified distance is at most the original one. -/
theorem bbfRawProjDist_le (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) :
    P.bbfRawProjDist Y X Z ≤ P.projDist Y X Z := by
  classical
  rw [bbfRawProjDist, if_neg (not_or_intro hYX hYZ)]
  exact csInf_le (P.bbfCandidateValues_bddBelow Y X Z)
    ⟨(X, Z), P.pair_mem_bbfCandidatePairs hYX hYZ, rfl⟩

/-- The raw BBF infimum is already symmetric; no post-hoc symmetrization is
needed. -/
theorem bbfRawProjDist_comm (P : ProjectionSystem V) (Y X Z : V) :
    P.bbfRawProjDist Y X Z = P.bbfRawProjDist Y Z X := by
  classical
  rw [bbfRawProjDist, bbfRawProjDist]
  have hor : Y = X ∨ Y = Z ↔ Y = Z ∨ Y = X := or_comm
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
  rcases hab with hgeneral | hleft | hright | horiginal
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
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) :
    P.projDist Y X Z - P.bbfRawProjDist Y X Z ≤ 2 * P.ξ := by
  classical
  rw [bbfRawProjDist, if_neg (not_or_intro hYX hYZ)]
  have hle : P.projDist Y X Z - 2 * P.ξ ≤
      sInf (P.bbfCandidateValues Y X Z) := by
    apply le_csInf (P.bbfCandidateValues_nonempty hYX hYZ)
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
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) :
    P.bbfProjDist Y X Z ≤ P.projDist Y X Z :=
  P.bbfRawProjDist_le hYX hYZ

theorem projDist_sub_bbfProjDist_le_two_mul
    (P : ProjectionSystem V) {Y X Z : V}
    (hYX : Y ≠ X) (hYZ : Y ≠ Z) :
    P.projDist Y X Z - P.bbfProjDist Y X Z ≤ 2 * P.ξ := by
  exact P.projDist_sub_bbfRawProjDist_le_two_mul hYX hYZ

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

/-- The raw BBF infimum is equivariant. -/
theorem bbfRawProjDist_smul (P : EquivariantProjectionSystem G V)
    (g : G) (Y X Z : V) :
    P.toProjectionSystem.bbfRawProjDist (g • Y) (g • X) (g • Z) =
      P.toProjectionSystem.bbfRawProjDist Y X Z := by
  classical
  rw [ProjectionSystem.bbfRawProjDist, ProjectionSystem.bbfRawProjDist]
  have hor : g • Y = g • X ∨ g • Y = g • Z ↔ Y = X ∨ Y = Z := by
    constructor
    · rintro (h | h)
      · exact Or.inl (smul_left_cancel g h)
      · exact Or.inr (smul_left_cancel g h)
    · rintro (rfl | rfl) <;> simp
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
