import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints

/-!
# The printed rank-twelve configuration

This module lifts the nested block calculations of
`Leavitt.RankTwelveCompressor` to the literal group
`EL₁₂(L_{𝔽₂}(1,2))` used in the manuscript.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

/-! ## Flattening elementary block matrices -/

theorem flat12_apply (M : RankTwelve.Full R) :
    flat12 M = Matrix.reindexRingEquiv R frame12
      (Matrix.compRingEquiv (Fin 2) (Fin 2 × Fin 3) R
        (((Matrix.compRingEquiv (Fin 2) (Fin 3) R).mapMatrix (m := Fin 2)) M)) :=
  rfl

theorem flat12_single (b c b' c' : Fin 2) (i j : Fin 3) (x : R) :
    flat12 (Matrix.single b c
      (Matrix.single b' c' (Matrix.single i j x))) =
      Matrix.single (frame12 (b, (b', i))) (frame12 (c, (c', j))) x := by
  have hinner : (Matrix.compRingEquiv (Fin 2) (Fin 3) R)
      (Matrix.single b' c' (Matrix.single i j x)) =
      Matrix.single (b', i) (c', j) x := by
    rw [Matrix.compRingEquiv_apply, Matrix.comp_single_single]
  rw [flat12_apply, RingEquiv.mapMatrix_apply,
    HilbertHotel.single_map_zero _
      (map_zero (Matrix.compRingEquiv (Fin 2) (Fin 3) R)),
    hinner, Matrix.compRingEquiv_apply, Matrix.comp_single_single,
    Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Equiv.symm_symm]

/-- The flattening equivalence on unit groups. -/
noncomputable def flat12Units : (RankTwelve.Full R)ˣ ≃*
    (Matrix (Fin 12) (Fin 12) R)ˣ :=
  Units.mapEquiv flat12.toMulEquiv

theorem flat12Units_elementary_single_mem
    (b c b' c' : Fin 2) (hbc : b ≠ c) (W : RankTwelve.Cell R) :
    flat12Units
        (elementaryUnit b c hbc (Matrix.single b' c' W)) ∈
      elementaryGroup (Fin 12) R := by
  induction W using Matrix.induction_on' with
  | h_zero =>
      rw [Matrix.single_zero, elementaryUnit_zero, map_one]
      exact one_mem _
  | h_add M N hM hN =>
      rw [Matrix.single_add, ← elementaryUnit_mul, map_mul]
      exact mul_mem hM hN
  | h_std_basis i j x =>
      have hne : frame12 (b, (b', i)) ≠ frame12 (c, (c', j)) := by
        intro hcon
        exact hbc (congrArg (fun p ↦ p.1)
          (frame12.injective hcon))
      have hval :
          flat12Units
              (elementaryUnit b c hbc
                (Matrix.single b' c' (Matrix.single i j x))) =
            elementaryUnit (frame12 (b, (b', i)))
              (frame12 (c, (c', j))) hne x := by
        apply Units.ext
        show flat12 ((1 : RankTwelve.Full R) +
            Matrix.single b c
              (Matrix.single b' c' (Matrix.single i j x))) =
          1 + Matrix.single (frame12 (b, (b', i)))
            (frame12 (c, (c', j))) x
        rw [map_add, map_one, flat12_single]
      rw [hval]
      exact elementaryUnit_mem _ _ _ _

theorem flat12Units_elementary_mem (b c : Fin 2) (hbc : b ≠ c)
    (Z : RankTwelve.Half R) :
    flat12Units (elementaryUnit b c hbc Z) ∈
      elementaryGroup (Fin 12) R := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
      rw [elementaryUnit_zero, map_one]
      exact one_mem _
  | h_add M N hM hN =>
      rw [← elementaryUnit_mul, map_mul]
      exact mul_mem hM hN
  | h_std_basis b' c' W =>
      exact flat12Units_elementary_single_mem b c b' c' hbc W

/-! ## The Whitehead word lies in `EL₁₂` -/

theorem outerElementary01_val (N : RankTwelve.Half R) :
    ((elementaryUnit (0 : Fin 2) 1 (by decide) N :
      (RankTwelve.Full R)ˣ) : RankTwelve.Full R) =
      RankTwelve.upperBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryUnit, RankTwelve.upperBlock, Matrix.one_fin_two]

theorem outerElementary10_val (N : RankTwelve.Half R) :
    ((elementaryUnit (1 : Fin 2) 0 (by decide) N :
      (RankTwelve.Full R)ˣ) : RankTwelve.Full R) =
      RankTwelve.lowerBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryUnit, RankTwelve.lowerBlock, Matrix.one_fin_two]

theorem tauUnit_eq_six_elementary :
    RankTwelve.tauUnit leavittFamily =
      elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
        elementaryUnit 1 0 (by decide) (-(RankTwelve.shiftInv leavittFamily)) *
        elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
        elementaryUnit 1 0 (by decide) 1 *
        elementaryUnit 0 1 (by decide) (-1) *
        elementaryUnit 1 0 (by decide) 1 := by
  apply Units.ext
  rw [RankTwelve.tauUnit_val]
  simpa only [Units.val_mul, outerElementary01_val, outerElementary10_val]
    using RankTwelve.tau_eq_whitehead_product leavittFamily

theorem printedTauGL_eq_flat12Units :
    printedTauGL = flat12Units (RankTwelve.tauUnit leavittFamily) := rfl

/-- The literal printed stable letter belongs to `EL₁₂`. -/
theorem printedTauGL_mem :
    printedTauGL ∈ elementaryGroup (Fin 12) R := by
  rw [printedTauGL_eq_flat12Units, tauUnit_eq_six_elementary]
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (flat12Units_elementary_mem 0 1 (by decide)
      (RankTwelve.shift leavittFamily))
    (flat12Units_elementary_mem 1 0 (by decide)
      (-(RankTwelve.shiftInv leavittFamily))))
    (flat12Units_elementary_mem 0 1 (by decide)
      (RankTwelve.shift leavittFamily)))
    (flat12Units_elementary_mem 1 0 (by decide) 1))
    (flat12Units_elementary_mem 0 1 (by decide) (-1)))
    (flat12Units_elementary_mem 1 0 (by decide) 1)

/-- The printed stable letter as an element of `H`. -/
noncomputable def tau : H := ⟨printedTauGL, printedTauGL_mem⟩

/-! ## The upper-left corner homomorphism -/

def fullCornerHom : RankTwelve.Cell R →* RankTwelve.Full R where
  toFun := RankTwelve.fullCorner
  map_one' := RankTwelve.fullCorner_one
  map_mul' M N := (RankTwelve.fullCorner_mul M N).symm

noncomputable def fullCornerUnits :
    (RankTwelve.Cell R)ˣ →* (RankTwelve.Full R)ˣ :=
  Units.map fullCornerHom

noncomputable def flatCornerUnits :
    (RankTwelve.Cell R)ˣ →* (Matrix (Fin 12) (Fin 12) R)ˣ :=
  flat12Units.toMonoidHom.comp fullCornerUnits

theorem flat12_fullCorner_elementary (i j : Fin 3) (a : R) :
    flat12 (RankTwelve.fullCorner
      (1 + Matrix.single i j a)) =
      1 + Matrix.single (cornerIndex i) (cornerIndex j) a := by
  rw [RankTwelve.fullCorner, RankTwelve.halfCorner,
    HilbertHotel.blockDiag_fst, HilbertHotel.blockDiag_fst,
    map_add, map_one, flat12_single]
  rfl

theorem flatCornerUnits_elementaryUnit (i j : Fin 3) (hij : i ≠ j)
    (a : R) :
    flatCornerUnits (elementaryUnit i j hij a) =
      elementaryUnit (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a := by
  apply Units.ext
  exact flat12_fullCorner_elementary i j a

theorem flatCornerUnits_mem_elementary
    (g : (RankTwelve.Cell R)ˣ)
    (hg : g ∈ elementaryGroup (Fin 3) R) :
    flatCornerUnits g ∈ elementaryGroup (Fin 12) R := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [flatCornerUnits_elementaryUnit]
      exact elementaryUnit_mem _ _ _ _
  | one => simp
  | mul x y _ _ hx hy => simpa using (elementaryGroup (Fin 12) R).mul_mem hx hy
  | inv x _ hx => simpa using (elementaryGroup (Fin 12) R).inv_mem hx

/-- The flattened corner map, with its range restricted to the ambient
elementary group. -/
noncomputable def flatCornerToH :
    (RankTwelve.Cell R)ˣ →* H :=
  flatCornerUnits.codRestrict (elementaryGroup (Fin 12) R)
    flatCornerUnits_mem_elementary

noncomputable def cornerEmbedding :
    BinaryLeavittSteinberg.ElementaryBase 3 →* H :=
  flatCornerToH.comp (elementaryGroup (Fin 3) R).subtype

@[simp] theorem cornerEmbedding_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    cornerEmbedding (elementaryRoot i j hij a) =
      elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a := by
  apply Subtype.ext
  exact flatCornerUnits_elementaryUnit i j hij a

theorem cornerEmbedding_range : cornerEmbedding.range = corner := by
  apply le_antisymm
  · have hle : elementaryGroup (Fin 3) R ≤
        corner.comap flatCornerToH := by
      rw [elementaryGroup, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, a, rfl⟩
      change flatCornerToH (elementaryUnit i j hij a) ∈ corner
      rw [flatCornerUnits_elementaryUnit]
      exact Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩
    rintro _ ⟨g, rfl⟩
    exact hle g.property
  · rw [corner, Subgroup.closure_le]
    rintro x ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryRoot i j hij a,
      cornerEmbedding_elementaryRoot i j hij a⟩

noncomputable def cornerEmbeddingToCorner :
    BinaryLeavittSteinberg.ElementaryBase 3 →* corner :=
  cornerEmbedding.codRestrict corner fun g ↦ by
    rw [← cornerEmbedding_range]
    exact ⟨g, rfl⟩

theorem cornerEmbeddingToCorner_surjective :
    Function.Surjective cornerEmbeddingToCorner := by
  intro x
  have hx : (x : H) ∈ cornerEmbedding.range := by
    rw [cornerEmbedding_range]
    exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

theorem corner_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} corner :=
  HasKazhdanPropertyT.of_surjective cornerEmbeddingToCorner
    cornerEmbeddingToCorner_surjective
    (BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT
      (n := 3) (by omega))

/-! ## Conjugation compresses the corner -/

theorem tauUnit_conj_fullCorner (u : (RankTwelve.Cell R)ˣ) :
    RankTwelve.tauUnit leavittFamily * fullCornerUnits u *
        (RankTwelve.tauUnit leavittFamily)⁻¹ =
      fullCornerUnits (leavittFamily.matrixCompressionHom u) := by
  apply Units.ext
  exact RankTwelve.tau_fullCorner_tauInv leavittFamily (u : RankTwelve.Cell R)

theorem tau_conj_corner_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    tau * elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a * tau⁻¹ =
      elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij)
        (leavittFamily.s0 * a * leavittFamily.t0) := by
  apply Subtype.ext
  change printedTauGL *
      elementaryUnit (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a * printedTauGL⁻¹ =
    elementaryUnit (cornerIndex i) (cornerIndex j)
      (cornerIndex_injective.ne hij)
      (leavittFamily.s0 * a * leavittFamily.t0)
  rw [← flatCornerUnits_elementaryUnit i j hij a,
    ← flatCornerUnits_elementaryUnit i j hij
      (leavittFamily.s0 * a * leavittFamily.t0)]
  have hraw := tauUnit_conj_fullCorner
    (elementaryUnit i j hij a)
  have hmapped := congrArg flat12Units hraw
  rw [leavittFamily.matrixCompression_elementaryUnit] at hmapped
  rw [printedTauGL_eq_flat12Units]
  change flat12Units (RankTwelve.tauUnit leavittFamily) *
      flat12Units (fullCornerUnits (elementaryUnit i j hij a)) *
        (flat12Units (RankTwelve.tauUnit leavittFamily))⁻¹ =
    flat12Units (fullCornerUnits
      (elementaryUnit i j hij
        (leavittFamily.s0 * a * leavittFamily.t0)))
  simpa only [map_mul, map_inv] using hmapped

/-- Conjugation by the literal printed `tau` maps the whole upper-left
`EL₃` corner into itself. -/
theorem tau_compresses_corner :
    ∀ gamma ∈ corner, tau * gamma * tau⁻¹ ∈ corner := by
  intro gamma hgamma
  rw [corner] at hgamma
  induction hgamma using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [tau_conj_corner_elementaryRoot i j hij a]
      exact Subgroup.subset_closure
        ⟨i, j, hij, leavittFamily.s0 * a * leavittFamily.t0, rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
      rw [show tau * (x * y) * tau⁻¹ =
          (tau * x * tau⁻¹) * (tau * y * tau⁻¹) by group]
      exact corner.mul_mem hx hy
  | inv x _ hx =>
      rw [show tau * x⁻¹ * tau⁻¹ = (tau * x * tau⁻¹)⁻¹ by group]
      exact corner.inv_mem hx

/-! ## The moved mark and the exact defect -/

/-- The `3 × 3` mark occupying the second block of the first half. -/
def mark3 : RankTwelve.Cell R := 1 + Matrix.single 0 1 1

theorem mark3_central (i j : Fin 3) (x : R) :
    mark3 i j * x = x * mark3 i j := by
  unfold mark3
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs
  · rw [add_mul, mul_add, one_mul, mul_one]
  · rw [add_zero, one_mul, mul_one]
  · rw [zero_add, one_mul, mul_one]
  · rw [add_zero, zero_mul, mul_zero]

theorem shift_mul_blockMark :
    RankTwelve.shift leavittFamily * !![1, 0; 0, mark3] =
      !![RankTwelve.kap leavittFamily.s0,
          RankTwelve.kap (leavittFamily.s1 * leavittFamily.t0) * mark3;
        0, RankTwelve.kap leavittFamily.t1 * mark3] := by
  rw [RankTwelve.shift, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Moving the second-block mark by `X` deposits `e₀₁(q)` in the first
block and leaves the mark itself fixed. -/
theorem shift_conj_mark :
    RankTwelve.shift leavittFamily * !![1, 0; 0, mark3] *
        RankTwelve.shiftInv leavittFamily =
      !![1 + Matrix.single 0 1 q, 0; 0, mark3] := by
  have e00 :
      RankTwelve.kap leavittFamily.s0 *
          RankTwelve.kap leavittFamily.t0 +
        RankTwelve.kap (leavittFamily.s1 * leavittFamily.t0) * mark3 *
          RankTwelve.kap (leavittFamily.s0 * leavittFamily.t1) =
      RankTwelve.kap leavittFamily.p0 +
        RankTwelve.kap leavittFamily.p1 * mark3 := by
    change Matrix.scalar (Fin 3) leavittFamily.s0 *
          Matrix.scalar (Fin 3) leavittFamily.t0 +
        Matrix.scalar (Fin 3) (leavittFamily.s1 * leavittFamily.t0) * mark3 *
          Matrix.scalar (Fin 3) (leavittFamily.s0 * leavittFamily.t1) =
      Matrix.scalar (Fin 3) leavittFamily.p0 +
        Matrix.scalar (Fin 3) leavittFamily.p1 * mark3
    rw [HilbertHotel.scalar_move _ _ mark3 mark3_central,
      ← map_mul (Matrix.scalar (Fin 3) (α := R)),
      HilbertHotel.s1r0_mul_s0r1]
    rfl
  have e01 :
      RankTwelve.kap leavittFamily.s0 * 0 +
        RankTwelve.kap (leavittFamily.s1 * leavittFamily.t0) * mark3 *
          RankTwelve.kap leavittFamily.s1 = 0 := by
    change Matrix.scalar (Fin 3) leavittFamily.s0 * 0 +
        Matrix.scalar (Fin 3) (leavittFamily.s1 * leavittFamily.t0) * mark3 *
          Matrix.scalar (Fin 3) leavittFamily.s1 = 0
    rw [mul_zero, zero_add,
      HilbertHotel.scalar_move _ _ mark3 mark3_central,
      HilbertHotel.s1r0_mul_s1, map_zero, zero_mul]
  have e10 :
      0 * RankTwelve.kap leavittFamily.t0 +
        RankTwelve.kap leavittFamily.t1 * mark3 *
          RankTwelve.kap (leavittFamily.s0 * leavittFamily.t1) = 0 := by
    change 0 * Matrix.scalar (Fin 3) leavittFamily.t0 +
        Matrix.scalar (Fin 3) leavittFamily.t1 * mark3 *
          Matrix.scalar (Fin 3) (leavittFamily.s0 * leavittFamily.t1) = 0
    rw [zero_mul, zero_add,
      HilbertHotel.scalar_move _ _ mark3 mark3_central,
      HilbertHotel.r1_mul_s0r1, map_zero, zero_mul]
  have e11 :
      0 * 0 + RankTwelve.kap leavittFamily.t1 * mark3 *
        RankTwelve.kap leavittFamily.s1 = mark3 := by
    change 0 * 0 + Matrix.scalar (Fin 3) leavittFamily.t1 * mark3 *
        Matrix.scalar (Fin 3) leavittFamily.s1 = mark3
    rw [zero_mul, zero_add,
      HilbertHotel.scalar_move _ _ mark3 mark3_central,
      leavittFamily.t1_s1, map_one, one_mul]
  have key : RankTwelve.kap leavittFamily.p0 +
      RankTwelve.kap leavittFamily.p1 * mark3 =
        1 + Matrix.single 0 1 q := by
    change Matrix.scalar (Fin 3) leavittFamily.p0 +
      Matrix.scalar (Fin 3) leavittFamily.p1 * mark3 =
        1 + Matrix.single 0 1 q
    unfold mark3 q
    rw [mul_add, mul_one, HilbertHotel.scalar_mul_single, mul_one,
      ← add_assoc,
      ← map_add (Matrix.scalar (Fin 3) (α := R))
        leavittFamily.p0 leavittFamily.p1,
      leavittFamily.p0_add_p1, map_one]
  rw [shift_mul_blockMark, RankTwelve.shiftInv, Matrix.mul_fin_two,
    e00, e01, e10, e11, key]

/-- The nested full-frame matrix representing `c=e₃₄(1)`. -/
def rawC : RankTwelve.Full R :=
  !![!![1, 0; 0, mark3], 0; 0, 1]

/-- The nested full-frame matrix produced after conjugating the mark. -/
def rawMovedC : RankTwelve.Full R :=
  !![!![1 + Matrix.single 0 1 q, 0; 0, mark3], 0; 0, 1]

theorem tau_conj_rawC :
    RankTwelve.tau leavittFamily * rawC *
        RankTwelve.tauInv leavittFamily = rawMovedC := by
  have hfirst : RankTwelve.tau leavittFamily * rawC =
      !![RankTwelve.shift leavittFamily * !![1, 0; 0, mark3], 0;
        0, RankTwelve.shiftInv leavittFamily] := by
    rw [RankTwelve.tau, rawC, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hfirst, RankTwelve.tauInv, rawMovedC, Matrix.mul_fin_two,
    shift_conj_mark, RankTwelve.shiftInv_mul_shift]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem flat12_rawC :
    flat12 rawC = 1 + Matrix.single (3 : Fin 12) 4 1 := by
  rw [rawC, mark3, HilbertHotel.blockDiag_snd,
    HilbertHotel.blockDiag_fst, map_add, map_one, flat12_single]
  rfl

theorem flat12_rawMovedC :
    flat12 rawMovedC =
      1 + Matrix.single (0 : Fin 12) 1 q +
        Matrix.single (3 : Fin 12) 4 1 := by
  rw [rawMovedC, mark3, HilbertHotel.blockDiag_both,
    HilbertHotel.blockDiag_fst, map_add, map_one, Matrix.single_add,
    map_add, flat12_single, flat12_single, add_assoc]
  rfl

theorem tau_conj_c :
    tau * c * tau⁻¹ =
      elementaryRoot (0 : Fin 12) 1 (by decide) q * c := by
  apply Subtype.ext
  apply Units.ext
  show flat12 (RankTwelve.tau leavittFamily) *
      (1 + Matrix.single (3 : Fin 12) 4 1) *
      flat12 (RankTwelve.tauInv leavittFamily) =
    (1 + Matrix.single (0 : Fin 12) 1 q) *
      (1 + Matrix.single (3 : Fin 12) 4 1)
  have hcross :
      (Matrix.single (0 : Fin 12) 1 q *
        Matrix.single (3 : Fin 12) 4 1 : Matrix (Fin 12) (Fin 12) R) = 0 := by
    apply Matrix.single_mul_single_of_ne
    decide
  have hleft : flat12 (RankTwelve.tau leavittFamily) *
      (1 + Matrix.single (3 : Fin 12) 4 1) *
      flat12 (RankTwelve.tauInv leavittFamily) =
        1 + Matrix.single (0 : Fin 12) 1 q +
          Matrix.single (3 : Fin 12) 4 1 := by
    rw [← flat12_rawC, ← map_mul, ← map_mul, tau_conj_rawC,
      flat12_rawMovedC]
  rw [hleft]
  noncomm_ring [hcross]

/-- The exact commutator identity of `prop:defect`. -/
theorem tau_c_commutator_ell :
    ⁅tau * c * tau⁻¹, ell⁆ = defect := by
  rw [tau_conj_c]
  have hc : Commute c ell := c_commutes_corner ell ell_mem_corner
  rw [HilbertHotel.commutator_mul_left_of_commute _ _ _ hc]
  simpa only [ell, defect, mul_one] using
    (elementaryRoot_commutator (R := R) (0 : Fin 12) 1 2
      (by decide) (by decide) (by decide) q 1)

/-- **`prop:defect`'s complete group-level configuration, closed.** -/
theorem printedDefectConfiguration : PrintedDefectConfiguration :=
  ⟨printedTauGL_mem, corner_hasKazhdanPropertyT,
    tau_compresses_corner, tau_c_commutator_ell⟩

/-- **`prop:defect`, exactly and without hypotheses.**  The transparent
definitions above are the manuscript's literal elements
`c=e₃₄(1)`, `ell=e₁₂(1)`, `d=e₀₂(q)`, and the flattened
`tau=diag(X,Y)`.  The four conjuncts below are precisely the proposition's
four assertions: centrality of `c` relative to the canonical upper-left
`EL₃`, the displayed commutator calculation, nontriviality of `d`, and
normal generation of `H`.  No simplicity input is consumed: normal generation
is the independently closed Steinberg-root theorem. -/
def PropositionDefect : Prop :=
  (∀ gamma ∈ corner, Commute c gamma) ∧
    ⁅tau * c * tau⁻¹, ell⁆ = defect ∧
    defect ≠ 1 ∧
    Subgroup.normalClosure ({defect} : Set H) = ⊤

theorem manuscriptPropositionDefect : PropositionDefect :=
  ⟨c_commutes_corner, tau_c_commutator_ell,
    defect_ne_one, normalClosure_defect_eq_top⟩

theorem rankTwelve_actualCoronaMFResidual_eq_top :
    actualCoronaMFResidual H = ⊤ :=
  residual_eq_top_of_configuration printedDefectConfiguration

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
