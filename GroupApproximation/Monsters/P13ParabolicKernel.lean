import GroupApproximation.Monsters.SL3BlockEmbedding
import GroupApproximation.Monsters.P13BlockSL2
import GroupApproximation.Monsters.P13LowerUnipotentInjectivity

/-!
# The parabolic subgroup of P13 meets the kernel trivially

The subgroup `H = ⟨e₁₂, e₂₁, e₃₁, e₃₂⟩` of `P13` is the pattern of the
stabilizer of the third basis column: a bottom row `N = ⟨e₃₁, e₃₂⟩`
normalized by the faithful rank-two block `Γ = ⟨e₁₂, e₂₁⟩`.  Every
element of `H` has the semidirect normal form `x₃₁(a) x₃₂(b) · γ` with
`γ` in the block copy of `SL₂(ℤ)`; the matrix model reads `γ` off the
top-left block and then `(a, b)` off the bottom row, so an element of
`H` killed by the matrix model is trivial.

This is the rank-peeling step of the completeness programme: once every
kernel element of `toSL3` is shown to lie in `H`, the kernel is
trivial.
-/

namespace GroupApproximation
namespace P13ParabolicKernel

open LiteralP13Presentation LiteralP13MatrixModel P13SteinbergCalculus
open P13SL2Comparison SL3BlockEmbedding SL2BraidPresentation
open P13UnipotentInjectivity P13LowerUnipotentInjectivity P13BlockSL2
open SL2Completeness

noncomputable section

/-- The parabolic generator set `e₁₂, e₂₁, e₃₁, e₃₂`. -/
def parGens : Set P13 :=
  {PresentedGroup.of 0, PresentedGroup.of 2,
    PresentedGroup.of 4, PresentedGroup.of 5}

/-- The parabolic subgroup. -/
def Hpar : Subgroup P13 := Subgroup.closure parGens

/-- The bottom-row pair, written `x₃₁(a) x₃₂(b)`. -/
def lowpair (a b : ℤ) : P13 := x 4 a * x 5 b

theorem lowpair_mul (a b a' b' : ℤ) :
    lowpair a b * lowpair a' b' = lowpair (a + a') (b + b') := by
  show x 4 a * x 5 b * (x 4 a' * x 5 b') = x 4 (a + a') * x 5 (b + b')
  calc x 4 a * x 5 b * (x 4 a' * x 5 b')
      = x 4 a * (x 5 b * x 4 a') * x 5 b' := by group
    _ = x 4 a * (x 4 a' * x 5 b) * x 5 b' := by
        rw [((x_commute_31_32 a' b).eq).symm]
    _ = (x 4 a * x 4 a') * (x 5 b * x 5 b') := by group
    _ = x 4 (a + a') * x 5 (b + b') := by rw [x_add, x_add]

theorem lowpair_inv (a b : ℤ) :
    (lowpair a b)⁻¹ = lowpair (-a) (-b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [lowpair_mul]
  show x 4 (a + -a) * x 5 (b + -b) = 1
  simp

/-! ## The block conjugation of the bottom row -/

/-- Conjugation by the first block generator. -/
private theorem conj_e12_lowpair (c a b : ℤ) :
    x 0 c * lowpair a b * (x 0 c)⁻¹ = lowpair a (b - a * c) := by
  show x 0 c * (x 4 a * x 5 b) * (x 0 c)⁻¹ = x 4 a * x 5 (b - a * c)
  calc x 0 c * (x 4 a * x 5 b) * (x 0 c)⁻¹
      = (x 0 c * x 4 a * (x 0 c)⁻¹) * (x 0 c * x 5 b * (x 0 c)⁻¹) := by
        group
    _ = (x 5 (-(a * c)) * x 4 a) * x 5 b := by
        rw [P13WeylCalculus.x_conj_rev_12_31 c a,
          show x 0 c * x 5 b * (x 0 c)⁻¹ = x 5 b from by
            rw [(x_commute_12_32 c b).eq]; group]
    _ = x 4 a * (x 5 (-(a * c)) * x 5 b) := by
        rw [((x_commute_31_32 a (-(a * c))).eq).symm]
        group
    _ = x 4 a * x 5 (-(a * c) + b) := by rw [x_add]
    _ = x 4 a * x 5 (b - a * c) := by ring_nf

/-- Conjugation by the second block generator. -/
private theorem conj_e21_lowpair (c a b : ℤ) :
    x 2 c * lowpair a b * (x 2 c)⁻¹ = lowpair (a - b * c) b := by
  show x 2 c * (x 4 a * x 5 b) * (x 2 c)⁻¹ = x 4 (a - b * c) * x 5 b
  calc x 2 c * (x 4 a * x 5 b) * (x 2 c)⁻¹
      = (x 2 c * x 4 a * (x 2 c)⁻¹) * (x 2 c * x 5 b * (x 2 c)⁻¹) := by
        group
    _ = x 4 a * (x 4 (-(b * c)) * x 5 b) := by
        rw [P13WeylCalculus.x_conj_rev_21_32 c b,
          show x 2 c * x 4 a * (x 2 c)⁻¹ = x 4 a from by
            rw [(x_commute_21_31 c a).eq]; group]
    _ = (x 4 a * x 4 (-(b * c))) * x 5 b := by group
    _ = x 4 (a + -(b * c)) * x 5 b := by rw [x_add]
    _ = x 4 (a - b * c) * x 5 b := by ring_nf

/-- The bottom-row pairs form a subgroup. -/
def Nsub : Subgroup P13 where
  carrier := {g | ∃ a b : ℤ, g = lowpair a b}
  mul_mem' := by
    rintro g h ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', lowpair_mul a b a' b'⟩
  one_mem' := ⟨0, 0, by
    show (1 : P13) = x 4 0 * x 5 0
    simp⟩
  inv_mem' := by
    rintro g ⟨a, b, rfl⟩
    exact ⟨-a, -b, lowpair_inv a b⟩

private theorem e12_mem_normalizer (c : ℤ) : x 0 c ∈ Subgroup.normalizer (Nsub : Set P13) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b - a * c, conj_e12_lowpair c a b⟩
  · rintro ⟨A, B, hAB⟩
    have hn : n = (x 0 c)⁻¹ * lowpair A B * x 0 c := by
      calc n = (x 0 c)⁻¹ * (x 0 c * n * (x 0 c)⁻¹) * x 0 c := by group
        _ = (x 0 c)⁻¹ * lowpair A B * x 0 c := by rw [← hAB]
    have hxc : (x 0 c)⁻¹ = x 0 (-c) := (x_neg 0 c).symm
    have hxc2 : x 0 c = (x 0 (-c))⁻¹ := by rw [← hxc, inv_inv]
    refine ⟨A, B - A * (-c), ?_⟩
    rw [hn, hxc, hxc2]
    exact conj_e12_lowpair (-c) A B

private theorem e21_mem_normalizer (c : ℤ) : x 2 c ∈ Subgroup.normalizer (Nsub : Set P13) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a - b * c, b, conj_e21_lowpair c a b⟩
  · rintro ⟨A, B, hAB⟩
    have hn : n = (x 2 c)⁻¹ * lowpair A B * x 2 c := by
      calc n = (x 2 c)⁻¹ * (x 2 c * n * (x 2 c)⁻¹) * x 2 c := by group
        _ = (x 2 c)⁻¹ * lowpair A B * x 2 c := by rw [← hAB]
    have hxc : (x 2 c)⁻¹ = x 2 (-c) := (x_neg 2 c).symm
    have hxc2 : x 2 c = (x 2 (-c))⁻¹ := by rw [← hxc, inv_inv]
    refine ⟨A - B * (-c), B, ?_⟩
    rw [hn, hxc, hxc2]
    exact conj_e21_lowpair (-c) A B

/-- The faithful block normalizes the bottom row. -/
theorem block_mem_normalizer (γ : SL2P) :
    sl2ToP13 γ ∈ Subgroup.normalizer (Nsub : Set P13) := by
  have hmem : γ ∈ (⊤ : Subgroup SL2P) := trivial
  rw [← PresentedGroup.closure_range_of] at hmem
  induction hmem using Subgroup.closure_induction with
  | mem g hgen =>
      obtain ⟨i, rfl⟩ := hgen
      match i with
      | 0 =>
          rw [sl2ToP13_of_zero]
          exact e12_mem_normalizer 1
      | 1 =>
          rw [sl2ToP13_of_one]
          exact e21_mem_normalizer (-1)
  | one =>
      rw [map_one]
      exact Subgroup.one_mem _
  | mul g h _ _ ihg ihh =>
      rw [map_mul]
      exact Subgroup.mul_mem _ ihg ihh
  | inv g _ ih =>
      rw [map_inv]
      exact Subgroup.inv_mem _ ih

theorem block_conj_lowpair (γ : SL2P) (a b : ℤ) :
    ∃ A B : ℤ,
      sl2ToP13 γ * lowpair a b * (sl2ToP13 γ)⁻¹ = lowpair A B := by
  have hmem := block_mem_normalizer γ
  rw [Subgroup.mem_normalizer_iff] at hmem
  exact (hmem (lowpair a b)).mp ⟨a, b, rfl⟩

/-! ## The semidirect normal form on the parabolic -/

/-- Every parabolic element is `x₃₁(a) x₃₂(b) · γ` with `γ` in the
faithful block. -/
theorem exists_parabolic_form {g : P13} (hg : g ∈ Hpar) :
    ∃ (a b : ℤ) (γ : SL2P), g = lowpair a b * sl2ToP13 γ := by
  induction hg using Subgroup.closure_induction with
  | mem g hgen =>
      simp only [parGens, Set.mem_insert_iff, Set.mem_singleton_iff]
        at hgen
      rcases hgen with h | h | h | h
      · exact ⟨0, 0, PresentedGroup.of 0, by
          rw [h, sl2ToP13_of_zero]
          show PresentedGroup.of 0 = x 4 0 * x 5 0 * x 0 1
          simp⟩
      · exact ⟨0, 0, (PresentedGroup.of 1)⁻¹, by
          rw [h, map_inv, sl2ToP13_of_one, ← x_neg]
          show PresentedGroup.of 2 = x 4 0 * x 5 0 * x 2 (- -1)
          simp⟩
      · exact ⟨1, 0, 1, by
          rw [h, map_one]
          show PresentedGroup.of 4 = x 4 1 * x 5 0 * 1
          simp⟩
      · exact ⟨0, 1, 1, by
          rw [h, map_one]
          show PresentedGroup.of 5 = x 4 0 * x 5 1 * 1
          simp⟩
  | one => exact ⟨0, 0, 1, by
      rw [map_one]
      show (1 : P13) = x 4 0 * x 5 0 * 1
      simp⟩
  | mul g h _ _ ihg ihh =>
      obtain ⟨a, b, γ, rfl⟩ := ihg
      obtain ⟨a', b', γ', rfl⟩ := ihh
      obtain ⟨A, B, hAB⟩ := block_conj_lowpair γ a' b'
      refine ⟨a + A, b + B, γ * γ', ?_⟩
      calc lowpair a b * sl2ToP13 γ * (lowpair a' b' * sl2ToP13 γ')
          = lowpair a b *
            (sl2ToP13 γ * lowpair a' b' * (sl2ToP13 γ)⁻¹) *
            (sl2ToP13 γ * sl2ToP13 γ') := by group
        _ = lowpair a b * lowpair A B *
            (sl2ToP13 γ * sl2ToP13 γ') := by rw [hAB]
        _ = lowpair (a + A) (b + B) * sl2ToP13 (γ * γ') := by
            rw [lowpair_mul, map_mul]
  | inv g _ ih =>
      obtain ⟨a, b, γ, rfl⟩ := ih
      obtain ⟨A, B, hAB⟩ := block_conj_lowpair γ⁻¹ (-a) (-b)
      refine ⟨A, B, γ⁻¹, ?_⟩
      calc (lowpair a b * sl2ToP13 γ)⁻¹
          = (sl2ToP13 γ)⁻¹ * (lowpair a b)⁻¹ := by group
        _ = (sl2ToP13 γ)⁻¹ * lowpair (-a) (-b) := by rw [lowpair_inv]
        _ = (sl2ToP13 γ⁻¹ * lowpair (-a) (-b) * (sl2ToP13 γ⁻¹)⁻¹) *
            sl2ToP13 γ⁻¹ := by
            rw [map_inv]
            group
        _ = lowpair A B * sl2ToP13 γ⁻¹ := by rw [hAB]

/-! ## Trivial kernel on the parabolic -/

theorem toSL3_lowpair (a b : ℤ) :
    (toSL3 (lowpair a b) : Matrix (Fin 3) (Fin 3) ℤ) =
      !![1, 0, 0; 0, 1, 0; a, b, 1] := by
  have h : lowpair a b = P13LowerUnipotentInjectivity.lower 0 a b := by
    show x 4 a * x 5 b = x 2 0 * x 4 a * x 5 b
    simp
  rw [h, toSL3_lower]

/-- **Parabolic kernel triviality.**  An element of the parabolic
subgroup that the matrix model kills is trivial. -/
theorem eq_one_of_mem_parabolic_of_map_eq_one {g : P13}
    (hg : g ∈ Hpar) (h1 : toSL3 g = 1) : g = 1 := by
  obtain ⟨a, b, γ, rfl⟩ := exists_parabolic_form hg
  have himg : (toSL3 (lowpair a b) : Matrix (Fin 3) (Fin 3) ℤ) *
      (blockEmbed (toSL2 γ) : Matrix (Fin 3) (Fin 3) ℤ) =
      (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
    have h2 := congrArg
      (fun M : SL3 => (M : Matrix (Fin 3) (Fin 3) ℤ)) h1
    rw [map_mul, toSL3_sl2ToP13] at h2
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    simpa using h2
  rw [toSL3_lowpair, blockEmbed_coe] at himg
  -- top-left block entries force the block to be the identity
  have e00 : (toSL2 γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 0) himg
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
      using this
  have e01 : (toSL2 γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 0 1) himg
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
      using this
  have e10 : (toSL2 γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 0) himg
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
      using this
  have e11 : (toSL2 γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 1 1) himg
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
      using this
  have hγmat : toSL2 γ = 1 := by
    apply Subtype.ext
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [Matrix.SpecialLinearGroup.coe_one, e00, e01, e10, e11]
  have hγ : γ = 1 := toSL2_injective (by rw [hγmat, map_one])
  subst hγ
  rw [map_one, mul_one]
  -- the bottom row entries force the pair to vanish
  have ha : a = 0 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 0) himg
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      hγmat, Matrix.SpecialLinearGroup.coe_one]
      using this
  have hb : b = 0 := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℤ => M 2 1) himg
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      hγmat, Matrix.SpecialLinearGroup.coe_one]
      using this
  rw [ha, hb]
  show x 4 0 * x 5 0 = 1
  simp

end

end P13ParabolicKernel
end GroupApproximation
