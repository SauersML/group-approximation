import GroupApproximation.CharClass.MappingTorusProjection

/-!
# Sections of the mapping torus, and their zeros

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`GroupApproximation/CharClass/MappingTorusProjection.lean` builds the mapping torus
`W_g` over `S¹ × M` by clutching two half-circle families along the two-point equator.
A section of `W_g` is therefore given by **two** vector fields: `ξ` on the closed northern
half `{t ≥ 0}` and `η` on the closed southern half `{t ≤ 0}`, matched along the equator
`{t = 0}` by the transition matrix.

The matching condition is `η = f *ᵥ ξ` on `{t = 0}`, where `f` is `G` at `y = 1` and the
identity at `y = -1`.  **The direction matters.**  Reading it at the two equator points:

* at `y = 1`  the southern field is `G` applied to the northern one;
* at `y = -1` the two fields agree.

So a section which is the constant `e` on the north and, on the south, the manuscript's
path `(2.10)` running from `e` (at `y = -1`) to `s` (at `y = 1`) descends **iff**
`G e = s`.  That is the manuscript's own normalisation `g e = s` (§2, the sentence
"Extending it by `e ↦ s` … yields a unitary bundle automorphism `g` of `V` satisfying
`g e = s`"); no adjoint has to be inserted.

## Main results

* `mappingTorus_eq` — the bundle in block normal form.
* `IsMTSectionData` — the two vector fields and their matching condition.
* `mtSection` — the resulting section, `mtSection_continuous`, `mtSection_mem`.
* `mtSection_eq_zero_iff` — **the zero locus**: on the closed northern half the section
  vanishes exactly where `ξ` does, on the open southern half exactly where `η` does.
  In particular a nowhere-vanishing `ξ` confines every zero to the southern half.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix

-- Statements below mention `n` only through `Matrix n n ℂ`, whose instances need fewer of
-- the section's typeclass arguments than the statements do.
set_option linter.unusedSectionVars false

section Section

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {M : Type*} [TopologicalSpace M] {Z : Type*} [TopologicalSpace Z]
variable {V G : M → Matrix n n ℂ} {y t : Z → ℝ} {ξ η : Z × M → n → ℂ} {p : Z × M}

/-- The mapping torus in block normal form. -/
theorem mappingTorus_eq (V G : M → Matrix n n ℂ) (y t : Z → ℝ) (p : Z × M) :
    mappingTorus V G y t p = Matrix.fromBlocks
      ((((1 + t p.1) / 2 : ℝ) : ℂ) • V p.2)
      ((2⁻¹ : ℂ) • ((mtTrans (G p.2) (y p.1))ᴴ * V p.2))
      ((2⁻¹ : ℂ) • (mtTrans (G p.2) (y p.1) * V p.2))
      ((((1 - t p.1) / 2 : ℝ) : ℂ) • V p.2) := by
  rw [mappingTorus, mtProj_eq, double, Matrix.fromBlocks_multiply]
  refine Matrix.fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero, add_zero]
  · rw [Matrix.mul_zero, zero_add, Matrix.smul_mul]
  · rw [Matrix.smul_mul, Matrix.mul_zero, add_zero]
  · rw [Matrix.mul_zero, zero_add, Matrix.smul_mul, Matrix.one_mul]

/-- A vector of `ℂ^{n ⊕ n}` in `Sum.elim` form vanishes iff both halves do. -/
theorem sumElim_eq_zero_iff {u v : n → ℂ} :
    Sum.elim u v = (0 : n ⊕ n → ℂ) ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
  · rintro ⟨hu, hv⟩
    funext i
    cases i with
    | inl i => simpa using congrFun hu i
    | inr i => simpa using congrFun hv i

theorem continuous_sumElim_left {X : Type*} [TopologicalSpace X] {u : X → n → ℂ}
    (hu : Continuous u) : Continuous fun x => Sum.elim (u x) (0 : n → ℂ) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => simpa using (continuous_apply i).comp hu
  | inr i => simpa using continuous_const

theorem continuous_sumElim_right {X : Type*} [TopologicalSpace X] {u : X → n → ℂ}
    (hu : Continuous u) : Continuous fun x => Sum.elim (0 : n → ℂ) (u x) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl i => simpa using continuous_const
  | inr i => simpa using (continuous_apply i).comp hu

/-- **The data of a section of the mapping torus.**  Two vector fields, each taking values
in the range of `V`, matched along the equator by the transition matrix. -/
structure IsMTSectionData (V G : M → Matrix n n ℂ) (y t : Z → ℝ)
    (ξ η : Z × M → n → ℂ) : Prop where
  /-- The northern field is continuous. -/
  continuous_north : Continuous ξ
  /-- The southern field is continuous. -/
  continuous_south : Continuous η
  /-- The northern field takes values in the range of `V`. -/
  north_mem : ∀ p, V p.2 *ᵥ ξ p = ξ p
  /-- The southern field takes values in the range of `V`. -/
  south_mem : ∀ p, V p.2 *ᵥ η p = η p
  /-- The two fields are matched along the equator: `η = f *ᵥ ξ` where `f` is `G` at
  `y = 1` and the identity at `y = -1`. -/
  seam : ∀ p, t p.1 = 0 → η p = mtTrans (G p.2) (y p.1) *ᵥ ξ p

/-- **The section of the mapping torus** determined by a pair of matched fields: the
northern field on `{t ≥ 0}`, the southern one on `{t < 0}`, each pushed into the fibre by
the bundle projection itself. -/
def mtSection (V G : M → Matrix n n ℂ) (y t : Z → ℝ) (ξ η : Z × M → n → ℂ)
    (p : Z × M) : n ⊕ n → ℂ :=
  if 0 ≤ t p.1 then mappingTorus V G y t p *ᵥ Sum.elim (ξ p) 0
  else mappingTorus V G y t p *ᵥ Sum.elim 0 (η p)

/-- The northern normal form of the section. -/
theorem mtSection_north_form (hmem : V p.2 *ᵥ ξ p = ξ p) (hp : 0 ≤ t p.1) :
    mtSection V G y t ξ η p = Sum.elim ((((1 + t p.1) / 2 : ℝ) : ℂ) • ξ p)
      ((2⁻¹ : ℂ) • (mtTrans (G p.2) (y p.1) *ᵥ ξ p)) := by
  rw [mtSection, if_pos hp, mappingTorus_eq, Matrix.fromBlocks_mulVec]
  congr 1
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, hmem]
    simp
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hmem]
    simp

/-- The southern normal form of the section. -/
theorem mtSection_south_form (hmem : V p.2 *ᵥ η p = η p) (hp : ¬ 0 ≤ t p.1) :
    mtSection V G y t ξ η p =
      Sum.elim ((2⁻¹ : ℂ) • ((mtTrans (G p.2) (y p.1))ᴴ *ᵥ η p))
        ((((1 - t p.1) / 2 : ℝ) : ℂ) • η p) := by
  rw [mtSection, if_neg hp, mappingTorus_eq, Matrix.fromBlocks_mulVec]
  congr 1
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hmem]
    simp
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, hmem]
    simp

/-- The southern normal form, valid on the whole closed southern half (including the
equator).  This is the shape the seam matching is checked in. -/
theorem mtSection_south_form' (hmem : V p.2 *ᵥ η p = η p) :
    mappingTorus V G y t p *ᵥ Sum.elim 0 (η p) =
      Sum.elim ((2⁻¹ : ℂ) • ((mtTrans (G p.2) (y p.1))ᴴ *ᵥ η p))
        ((((1 - t p.1) / 2 : ℝ) : ℂ) • η p) := by
  rw [mappingTorus_eq, Matrix.fromBlocks_mulVec]
  congr 1
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hmem]
    simp
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, hmem]
    simp

/-- The northern normal form on the whole closed northern half. -/
theorem mtSection_north_form' (hmem : V p.2 *ᵥ ξ p = ξ p) :
    mappingTorus V G y t p *ᵥ Sum.elim (ξ p) 0 =
      Sum.elim ((((1 + t p.1) / 2 : ℝ) : ℂ) • ξ p)
        ((2⁻¹ : ℂ) • (mtTrans (G p.2) (y p.1) *ᵥ ξ p)) := by
  rw [mappingTorus_eq, Matrix.fromBlocks_mulVec]
  congr 1
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, hmem]
    simp
  · rw [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hmem]
    simp

/-- **The two branches agree on the equator.**  This is the gluing computation: the
transition matrix is an isometry there, so `fᴴ *ᵥ (f *ᵥ ξ) = ξ`. -/
theorem mtSection_branches_agree (hd : IsMTSectionData V G y t ξ η)
    (hcu : ∀ m, IsCornerUnitary (V m) (G m)) (hch : IsCircleChart y t) {p : Z × M}
    (hp : t p.1 = 0) :
    mappingTorus V G y t p *ᵥ Sum.elim (ξ p) 0
      = mappingTorus V G y t p *ᵥ Sum.elim 0 (η p) := by
  have hseam := hd.seam p hp
  have hiso := mtTrans_star_mul_self (hcu p.2) (hch.circle p.1)
  rw [mtSection_north_form' (hd.north_mem p), mtSection_south_form' (hd.south_mem p)]
  have hback : (mtTrans (G p.2) (y p.1))ᴴ *ᵥ η p = ξ p := by
    rw [hseam, Matrix.mulVec_mulVec, hiso, hp]
    rw [show ((1 - (0 : ℝ) ^ 2 : ℝ) : ℂ) = 1 by norm_num, one_smul, Matrix.one_mulVec]
  congr 1
  · rw [hback, hp]
    congr 1
    push_cast
    norm_num
  · rw [hseam, hp]
    congr 1
    push_cast
    norm_num

/-- **The section is continuous.** -/
theorem mtSection_continuous (hd : IsMTSectionData V G y t ξ η)
    (hcu : ∀ m, IsCornerUnitary (V m) (G m)) (hch : IsCircleChart y t)
    (hV : Continuous V) (hG : Continuous G) :
    Continuous (mtSection V G y t ξ η) := by
  have hW : Continuous (mappingTorus V G y t) := mappingTorus_continuous hV hG hch
  have ht : Continuous fun p : Z × M => t p.1 := hch.continuous_height.comp continuous_fst
  simp only [mtSection]
  refine Continuous.if_le (hW.matrix_mulVec (continuous_sumElim_left hd.continuous_north))
    (hW.matrix_mulVec (continuous_sumElim_right hd.continuous_south)) continuous_const ht
    (fun p hp => ?_)
  exact mtSection_branches_agree hd hcu hch hp.symm

/-- **The section really is a section of `W_g`.** -/
theorem mtSection_mem (hcu : ∀ m, IsCornerUnitary (V m) (G m)) (hch : IsCircleChart y t)
    (p : Z × M) :
    mappingTorus V G y t p *ᵥ mtSection V G y t ξ η p = mtSection V G y t ξ η p := by
  have hidem := (mappingTorus_isStarProjection hcu hch p).isIdempotentElem.eq
  rw [mtSection]
  split_ifs with h <;> rw [Matrix.mulVec_mulVec, hidem]

/-! ### The zero locus -/

/-- **The zero locus of the section.**  On the closed northern half the section vanishes
exactly where the northern field does; on the open southern half, exactly where the
southern field does.  Nothing here uses a derivative, an orientation or a count. -/
theorem mtSection_eq_zero_iff (hd : IsMTSectionData V G y t ξ η) (p : Z × M) :
    mtSection V G y t ξ η p = 0 ↔ (if 0 ≤ t p.1 then ξ p = 0 else η p = 0) := by
  by_cases hp : 0 ≤ t p.1
  · rw [if_pos hp, mtSection_north_form (hd.north_mem p) hp, sumElim_eq_zero_iff]
    have hne : ((((1 + t p.1) / 2 : ℝ)) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (1 + t p.1) / 2 := by linarith
      exact_mod_cast this.ne'
    constructor
    · rintro ⟨h1, -⟩
      exact (smul_eq_zero.mp h1).resolve_left hne
    · intro h
      refine ⟨by rw [h, smul_zero], ?_⟩
      rw [h, Matrix.mulVec_zero, smul_zero]
  · rw [if_neg hp, mtSection_south_form (hd.south_mem p) hp, sumElim_eq_zero_iff]
    have hne : ((((1 - t p.1) / 2 : ℝ)) : ℂ) ≠ 0 := by
      have hlt : t p.1 < 0 := lt_of_not_ge hp
      have : (0 : ℝ) < (1 - t p.1) / 2 := by linarith
      exact_mod_cast this.ne'
    constructor
    · rintro ⟨-, h2⟩
      exact (smul_eq_zero.mp h2).resolve_left hne
    · intro h
      refine ⟨?_, by rw [h, smul_zero]⟩
      rw [h, Matrix.mulVec_zero, smul_zero]

/-- **A nowhere-vanishing northern field pushes every zero into the southern half.** -/
theorem mtSection_ne_zero_of_nonneg (hd : IsMTSectionData V G y t ξ η) {p : Z × M}
    (hp : 0 ≤ t p.1) (hξ : ξ p ≠ 0) : mtSection V G y t ξ η p ≠ 0 := by
  rw [mtSection_eq_zero_iff hd, if_pos hp]
  exact hξ

/-- **The zero locus when the northern field never vanishes.** -/
theorem mtSection_eq_zero_iff_of_north_ne_zero (hd : IsMTSectionData V G y t ξ η)
    (hξ : ∀ p, ξ p ≠ 0) (p : Z × M) :
    mtSection V G y t ξ η p = 0 ↔ (t p.1 < 0 ∧ η p = 0) := by
  rw [mtSection_eq_zero_iff hd]
  by_cases hp : 0 ≤ t p.1
  · rw [if_pos hp]
    simp only [not_lt.mpr hp, false_and, iff_false]
    exact hξ p
  · rw [if_neg hp]
    simp [lt_of_not_ge hp]

end Section

end GroupApproximation.CharClass
