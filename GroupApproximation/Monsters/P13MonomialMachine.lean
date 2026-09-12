import GroupApproximation.Monsters.P13WeylFourthPowers
import GroupApproximation.Monsters.P13ColumnLift
import GroupApproximation.Monsters.P13ParabolicKernel

/-!
# The finite monomial machine of the P13 presentation

The signed-swap subgroup `⟨w13, w23⟩` of `P13` maps onto the group of
determinant-one signed permutation matrices, of order twenty-four.
Over `ℤ` the only units are `±1`, so this subgroup is governed by
finitely many word identities, and the symbol calculus of Milnor's
§9.11 collapses to a six-coset Schreier argument: the orbit of `e₃`
consists of the six signed basis columns, with representatives

  `e₃ ↦ 1, e₁ ↦ w13, e₂ ↦ w23, -e₃ ↦ w13², -e₁ ↦ w13³, -e₂ ↦ w23·w13²`,

and every Schreier element is a power of the block Weyl element `w`.
The normal form — every element of `⟨w13, w23⟩` is a representative
times a power of `w` — follows by left closure induction from twelve
step identities, all deriving from three letter-wise conjugation
primitives, the braid relation, and the killed fourth powers.  Since
the powers of `w` lie in the parabolic subgroup, any element of
`⟨w13, w23⟩` whose matrix fixes `e₃` is parabolic: the endgame the
descent argument needs.
-/

namespace GroupApproximation
namespace P13MonomialMachine

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus
open P13WeylFourthPowers P13UnipotentInjectivity
open P13LowerUnipotentInjectivity
open P13ColumnLift P13ParabolicKernel

noncomputable section

/-! ## Inverse spellings and fourth-power absorption -/

theorem w23_inv_word : w23⁻¹ = x 3 (-1) * x 5 1 * x 3 (-1) := by
  show (x 3 1 * x 5 (-1) * x 3 1)⁻¹ = x 3 (-1) * x 5 1 * x 3 (-1)
  simp only [x]
  group

private theorem w4 : w * (w * (w * w)) = 1 := by
  have h := w_pow_four
  calc w * (w * (w * w)) = w * w * w * w := by group
    _ = 1 := h

private theorem w13four : w13 * (w13 * (w13 * w13)) = 1 := by
  have h := w13_pow_four
  calc w13 * (w13 * (w13 * w13)) = w13 * w13 * w13 * w13 := by group
    _ = 1 := h

private theorem w23four : w23 * (w23 * (w23 * w23)) = 1 := by
  have h := w23_pow_four
  calc w23 * (w23 * (w23 * w23)) = w23 * w23 * w23 * w23 := by group
    _ = 1 := h

theorem w_inv_eq_cube : w⁻¹ = w * (w * w) := by
  calc w⁻¹ = w⁻¹ * (w * (w * (w * w))) := by rw [w4]; group
    _ = w * (w * w) := by group

theorem w13_inv_eq_cube : w13⁻¹ = w13 * (w13 * w13) := by
  calc w13⁻¹ = w13⁻¹ * (w13 * (w13 * (w13 * w13))) := by
        rw [w13four]; group
    _ = w13 * (w13 * w13) := by group

theorem w23_inv_eq_cube : w23⁻¹ = w23 * (w23 * w23) := by
  calc w23⁻¹ = w23⁻¹ * (w23 * (w23 * (w23 * w23))) := by
        rw [w23four]; group
    _ = w23 * (w23 * w23) := by group

theorem wsq_inv : (w * w)⁻¹ = w * w := by
  have h : (w * w) * (w * w) = 1 := by
    calc (w * w) * (w * w) = w * (w * (w * w)) := by group
      _ = 1 := w4
  exact inv_eq_of_mul_eq_one_left h

theorem w13sq_inv : (w13 * w13)⁻¹ = w13 * w13 := by
  have h : (w13 * w13) * (w13 * w13) = 1 := by
    calc (w13 * w13) * (w13 * w13) = w13 * (w13 * (w13 * w13)) := by
          group
      _ = 1 := w13four
  exact inv_eq_of_mul_eq_one_left h

/-- Conjugating a three-letter word letter by letter. -/
private theorem conj_word (g a b c : P13) :
    g * (a * b * c) * g⁻¹ =
      (g * a * g⁻¹) * (g * b * g⁻¹) * (g * c * g⁻¹) := by
  group

/-! ## The three letter-wise conjugation primitives -/

/-- `w23 · w13 · w23⁻¹ = w`. -/
theorem w23_conj_w13 : w23 * w13 * w23⁻¹ = w := by
  have h : w23 * w13 * w23⁻¹ =
      (w23 * x 1 1 * w23⁻¹) * (w23 * x 4 (-1) * w23⁻¹) *
        (w23 * x 1 1 * w23⁻¹) := by
    show w23 * (x 1 1 * x 4 (-1) * x 1 1) * w23⁻¹ = _
    exact conj_word w23 _ _ _
  rw [h, w23_conj_13, w23_conj_31]
  rfl

/-- `w13 · w23 · w13⁻¹ = w⁻¹`. -/
theorem w13_conj_w23 : w13 * w23 * w13⁻¹ = w⁻¹ := by
  have h : w13 * w23 * w13⁻¹ =
      (w13 * x 3 1 * w13⁻¹) * (w13 * x 5 (-1) * w13⁻¹) *
        (w13 * x 3 1 * w13⁻¹) := by
    show w13 * (x 3 1 * x 5 (-1) * x 3 1) * w13⁻¹ = _
    exact conj_word w13 _ _ _
  rw [h, w13_conj_23, w13_conj_32]
  -- goal: x 2 1 * x 0 (-1) * x 2 1 = w⁻¹
  have hinv : x 2 1 * x 0 (-1) * x 2 1 =
      (x 2 (-1) * x 0 1 * x 2 (-1))⁻¹ := by
    simp only [x]
    group
  rw [hinv, ← braid]
  rfl

/-- `w · w13 · w⁻¹ = w23⁻¹`. -/
theorem w_conj_w13 : w * w13 * w⁻¹ = w23⁻¹ := by
  have h : w * w13 * w⁻¹ =
      (w * x 1 1 * w⁻¹) * (w * x 4 (-1) * w⁻¹) * (w * x 1 1 * w⁻¹) := by
    show w * (x 1 1 * x 4 (-1) * x 1 1) * w⁻¹ = _
    exact conj_word w _ _ _
  rw [h, w_conj_13, w_conj_31, w23_inv_word]
  norm_num

/-! ## Derived straightening identities -/

/-- `w13 · w23 = w⁻¹ · w13`. -/
theorem w13_mul_w23 : w13 * w23 = w⁻¹ * w13 := by
  have h := w13_conj_w23
  calc w13 * w23 = (w13 * w23 * w13⁻¹) * w13 := by group
    _ = w⁻¹ * w13 := by rw [h]

/-- `w23 · w13 = w · w23`. -/
theorem w23_mul_w13 : w23 * w13 = w * w23 := by
  have h := w23_conj_w13
  calc w23 * w13 = (w23 * w13 * w23⁻¹) * w23 := by group
    _ = w * w23 := by rw [h]

/-- `w · w23 = w13 · w`. -/
theorem w_mul_w23 : w * w23 = w13 * w := by
  have h := w13_eq_conj
  calc w * w23 = (w * w23 * w⁻¹) * w := by group
    _ = w13 * w := by rw [← h]

/-- `w13 · w = w23 · w13`. -/
theorem w13_mul_w : w13 * w = w23 * w13 := by
  have h := w13_conj_w
  calc w13 * w = (w13 * w * w13⁻¹) * w13 := by group
    _ = w23 * w13 := by rw [h]

/-- `w13² · w = w⁻¹ · w13²`. -/
theorem w13sq_mul_w : (w13 * w13) * w = w⁻¹ * (w13 * w13) := by
  calc (w13 * w13) * w = w13 * (w13 * w) := by group
    _ = w13 * (w23 * w13) := by rw [w13_mul_w]
    _ = (w13 * w23) * w13 := by group
    _ = (w⁻¹ * w13) * w13 := by rw [w13_mul_w23]
    _ = w⁻¹ * (w13 * w13) := by group

/-- `w23 · w⁻¹ = w⁻¹ · w13`. -/
theorem w23_mul_winv : w23 * w⁻¹ = w⁻¹ * w13 := by
  have h := w_mul_w23
  calc w23 * w⁻¹ = w⁻¹ * (w * w23) * w⁻¹ := by group
    _ = w⁻¹ * (w13 * w) * w⁻¹ := by rw [h]
    _ = w⁻¹ * w13 := by group

/-- `w⁻¹ · w23 = w13⁻¹ · w⁻¹`. -/
theorem winv_mul_w23 : w⁻¹ * w23 = w13⁻¹ * w⁻¹ := by
  have h := w_conj_w13
  have h3 : w * w13⁻¹ * w⁻¹ = w23 := by
    calc w * w13⁻¹ * w⁻¹ = (w * w13 * w⁻¹)⁻¹ := by group
      _ = (w23⁻¹)⁻¹ := by rw [h]
      _ = w23 := by group
  calc w⁻¹ * w23 = w⁻¹ * (w * w13⁻¹ * w⁻¹) := by rw [h3]
    _ = w13⁻¹ * w⁻¹ := by group

/-- `w23 · w13⁻¹ = w⁻¹ · w23`. -/
theorem w23_mul_w13inv : w23 * w13⁻¹ = w⁻¹ * w23 := by
  have h := w23_mul_w13
  calc w23 * w13⁻¹ = w⁻¹ * (w23 * w13) * w13⁻¹ * w23⁻¹ * w23 := by
        calc w23 * w13⁻¹
            = w⁻¹ * (w * w23) * w13⁻¹ * w23⁻¹ * w23 := by group
          _ = w⁻¹ * (w23 * w13) * w13⁻¹ * w23⁻¹ * w23 := by rw [← h]
    _ = w⁻¹ * w23 := by group

/-- The sign identity `w23² = w² · w13²`: the residue of the classical
`{-1,-1}` computation, closed by the killed fourth power. -/
theorem w23_sq : w23 * w23 = (w * w) * (w13 * w13) := by
  have hi : (w13 * w13) * w23 * (w13 * w13)⁻¹ = w23⁻¹ := by
    calc (w13 * w13) * w23 * (w13 * w13)⁻¹
        = w13 * (w13 * w23 * w13⁻¹) * w13⁻¹ := by group
      _ = w13 * w⁻¹ * w13⁻¹ := by rw [w13_conj_w23]
      _ = (w13 * w * w13⁻¹)⁻¹ := by group
      _ = w23⁻¹ := by rw [w13_conj_w]
  have hii : w23 * (w13 * w13)⁻¹ * w23⁻¹ = w⁻¹ * w⁻¹ := by
    calc w23 * (w13 * w13)⁻¹ * w23⁻¹
        = (w23 * w13 * w23⁻¹)⁻¹ * (w23 * w13 * w23⁻¹)⁻¹ := by group
      _ = w⁻¹ * w⁻¹ := by rw [w23_conj_w13]
  have hcomb : w23⁻¹ * w23⁻¹ = (w13 * w13) * (w⁻¹ * w⁻¹) := by
    calc w23⁻¹ * w23⁻¹
        = ((w13 * w13) * w23 * (w13 * w13)⁻¹) * w23⁻¹ := by rw [hi]
      _ = (w13 * w13) * (w23 * (w13 * w13)⁻¹ * w23⁻¹) := by group
      _ = (w13 * w13) * (w⁻¹ * w⁻¹) := by rw [hii]
  have hfin : w23 * w23 = (w * w) * (w13 * w13)⁻¹ := by
    calc w23 * w23 = (w23⁻¹ * w23⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
      _ = ((w13 * w13) * (w⁻¹ * w⁻¹))⁻¹ := by rw [hcomb]
      _ = (w * w) * (w13 * w13)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, inv_inv]
  rw [hfin, w13sq_inv]

/-- `w²` and `w13²` commute. -/
theorem wsq_comm_w13sq : (w * w) * (w13 * w13) = (w13 * w13) * (w * w) := by
  have h1 : (w13 * w13) * (w * w) = (w⁻¹ * w⁻¹) * (w13 * w13) := by
    calc (w13 * w13) * (w * w)
        = ((w13 * w13) * w) * w := by group
      _ = (w⁻¹ * (w13 * w13)) * w := by rw [w13sq_mul_w]
      _ = w⁻¹ * ((w13 * w13) * w) := by group
      _ = w⁻¹ * (w⁻¹ * (w13 * w13)) := by rw [w13sq_mul_w]
      _ = (w⁻¹ * w⁻¹) * (w13 * w13) := by group
  have h2 : w⁻¹ * w⁻¹ = w * w := by
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
      _ = w * w := wsq_inv
  rw [h1, h2]

/-- `w13⁴ = 1` in the pairing shape. -/
theorem w13sq_sq : (w13 * w13) * (w13 * w13) = 1 := by
  calc (w13 * w13) * (w13 * w13) = w13 * (w13 * (w13 * w13)) := by group
    _ = 1 := w13four

/-! ## Representatives, vectors, and `w`-powers -/

/-- The coset representatives, indexed by the six signed basis columns
in the order `e₃, e₁, e₂, -e₃, -e₁, -e₂`. -/
def repw : Fin 6 → P13
  | 0 => 1
  | 1 => w13
  | 2 => w23
  | 3 => w13 * w13
  | 4 => w13 * (w13 * w13)
  | 5 => w23 * (w13 * w13)

/-- The signed basis column carried by each representative. -/
def repVec : Fin 6 → (Fin 3 → ℤ)
  | 0 => ![0, 0, 1]
  | 1 => ![1, 0, 0]
  | 2 => ![0, 1, 0]
  | 3 => ![0, 0, -1]
  | 4 => ![-1, 0, 0]
  | 5 => ![0, -1, 0]

/-- Powers of the block Weyl element. -/
def wpow : Fin 4 → P13
  | 0 => 1
  | 1 => w
  | 2 => w * w
  | 3 => w * (w * w)

theorem wpow_mem_Hpar (k : Fin 4) : wpow k ∈ Hpar := by
  have h0 : (PresentedGroup.of 0 : P13) ∈ Hpar :=
    Subgroup.subset_closure (by simp [parGens])
  have h2 : (PresentedGroup.of 2 : P13) ∈ Hpar :=
    Subgroup.subset_closure (by simp [parGens])
  have hw : w ∈ Hpar := by
    have hx0 : x 0 1 ∈ Hpar := by rw [x_one]; exact h0
    have hx2 : x 2 (-1) ∈ Hpar := by
      rw [x_neg, x_one]
      exact Subgroup.inv_mem _ h2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx0 hx2) hx0
  match k with
  | 0 => exact Subgroup.one_mem _
  | 1 => exact hw
  | 2 => exact Subgroup.mul_mem _ hw hw
  | 3 => exact Subgroup.mul_mem _ hw (Subgroup.mul_mem _ hw hw)

/-- `w`-powers absorb products. -/
theorem wpow_mul_exists (j k : Fin 4) :
    ∃ l : Fin 4, wpow j * wpow k = wpow l := by
  fin_cases j
  · exact ⟨k, by show (1 : P13) * wpow k = wpow k; exact one_mul _⟩
  · fin_cases k
    · exact ⟨1, by show w * 1 = w; exact mul_one w⟩
    · exact ⟨⟨2, by omega⟩, rfl⟩
    · exact ⟨⟨3, by omega⟩, rfl⟩
    · exact ⟨0, w4⟩
  · fin_cases k
    · exact ⟨2, by show (w * w) * 1 = w * w; exact mul_one _⟩
    · exact ⟨3, by show (w * w) * w = w * (w * w); group⟩
    · refine ⟨0, ?_⟩
      show (w * w) * (w * w) = 1
      calc (w * w) * (w * w) = w * (w * (w * w)) := by group
        _ = 1 := w4
    · refine ⟨1, ?_⟩
      show (w * w) * (w * (w * w)) = w
      calc (w * w) * (w * (w * w))
          = w * (w * (w * (w * w))) := by group
        _ = w * 1 := by rw [w4]
        _ = w := mul_one w
  · fin_cases k
    · exact ⟨3, by show (w * (w * w)) * 1 = w * (w * w); exact mul_one _⟩
    · refine ⟨0, ?_⟩
      show (w * (w * w)) * w = 1
      calc (w * (w * w)) * w = w * (w * (w * w)) := by group
        _ = 1 := w4
    · refine ⟨1, ?_⟩
      show (w * (w * w)) * (w * w) = w
      calc (w * (w * w)) * (w * w)
          = (w * (w * (w * w))) * w := by group
        _ = 1 * w := by rw [w4]
        _ = w := one_mul w
    · refine ⟨2, ?_⟩
      show (w * (w * w)) * (w * (w * w)) = w * w
      calc (w * (w * w)) * (w * (w * w))
          = (w * (w * (w * w))) * (w * w) := by group
        _ = 1 * (w * w) := by rw [w4]
        _ = w * w := one_mul _

/-! ## The twelve Schreier steps -/

/-- Left multiplication by `w13` on the representatives. -/
theorem w13_mul_repw (j : Fin 6) :
    ∃ (j' : Fin 6) (k : Fin 4), w13 * repw j = repw j' * wpow k := by
  fin_cases j
  · exact ⟨1, 0, by show w13 * 1 = w13 * 1; rfl⟩
  · exact ⟨3, 0, by show w13 * w13 = w13 * w13 * 1; group⟩
  · -- w13·w23 = w⁻¹·w13 = w23·w⁻¹ = w23·w³
    refine ⟨2, 3, ?_⟩
    show w13 * w23 = w23 * wpow 3
    calc w13 * w23 = w⁻¹ * w13 := w13_mul_w23
      _ = w23 * w⁻¹ := w23_mul_winv.symm
      _ = w23 * (w * (w * w)) := by rw [w_inv_eq_cube]
      _ = w23 * wpow 3 := rfl
  · exact ⟨4, 0, by
      show w13 * (w13 * w13) = w13 * (w13 * w13) * 1
      group⟩
  · refine ⟨0, 0, ?_⟩
    show w13 * (w13 * (w13 * w13)) = 1 * wpow 0
    rw [w13four]
    rfl
  · -- w13·(w23·w13²) = (w23·w13²)·w
    refine ⟨5, 1, ?_⟩
    show w13 * (w23 * (w13 * w13)) = w23 * (w13 * w13) * wpow 1
    calc w13 * (w23 * (w13 * w13))
        = (w13 * w23) * (w13 * w13) := by group
      _ = (w⁻¹ * w13) * (w13 * w13) := by rw [w13_mul_w23]
      _ = (w23 * w⁻¹) * (w13 * w13) := by rw [← w23_mul_winv]
      _ = w23 * (w⁻¹ * (w13 * w13)) := by group
      _ = w23 * ((w13 * w13) * w) := by rw [← w13sq_mul_w]
      _ = w23 * (w13 * w13) * w := by group
      _ = w23 * (w13 * w13) * wpow 1 := rfl

/-- Left multiplication by `w23` on the representatives. -/
theorem w23_mul_repw (j : Fin 6) :
    ∃ (j' : Fin 6) (k : Fin 4), w23 * repw j = repw j' * wpow k := by
  fin_cases j
  · exact ⟨2, 0, by show w23 * 1 = w23 * 1; rfl⟩
  · -- w23·w13 = w·w23 = w13·w
    refine ⟨1, 1, ?_⟩
    show w23 * w13 = w13 * wpow 1
    calc w23 * w13 = w * w23 := w23_mul_w13
      _ = w13 * w := w_mul_w23
      _ = w13 * wpow 1 := rfl
  · -- w23² = w²·w13² = w13²·w²
    refine ⟨3, 2, ?_⟩
    show w23 * w23 = (w13 * w13) * wpow 2
    calc w23 * w23 = (w * w) * (w13 * w13) := w23_sq
      _ = (w13 * w13) * (w * w) := wsq_comm_w13sq
      _ = (w13 * w13) * wpow 2 := rfl
  · exact ⟨5, 0, by
      show w23 * (w13 * w13) = w23 * (w13 * w13) * 1
      group⟩
  · -- w23·w13³ = w23·w13⁻¹ = w⁻¹·w23 = w13⁻¹·w⁻¹ = w13³·w³
    refine ⟨4, 3, ?_⟩
    show w23 * (w13 * (w13 * w13)) = w13 * (w13 * w13) * wpow 3
    calc w23 * (w13 * (w13 * w13))
        = w23 * w13⁻¹ := by rw [← w13_inv_eq_cube]
      _ = w⁻¹ * w23 := w23_mul_w13inv
      _ = w13⁻¹ * w⁻¹ := winv_mul_w23
      _ = (w13 * (w13 * w13)) * (w * (w * w)) := by
          rw [← w13_inv_eq_cube, ← w_inv_eq_cube]
      _ = w13 * (w13 * w13) * wpow 3 := rfl
  · -- w23·(w23·w13²) = w23²·w13² = w²·w13⁴ = w²
    refine ⟨0, 2, ?_⟩
    show w23 * (w23 * (w13 * w13)) = 1 * wpow 2
    calc w23 * (w23 * (w13 * w13))
        = (w23 * w23) * (w13 * w13) := by group
      _ = ((w * w) * (w13 * w13)) * (w13 * w13) := by rw [w23_sq]
      _ = (w * w) * ((w13 * w13) * (w13 * w13)) := by group
      _ = (w * w) * 1 := by rw [w13sq_sq]
      _ = 1 * wpow 2 := by
          show (w * w) * 1 = 1 * (w * w)
          group

/-! ## The matrix action of the machine -/

theorem toSL3_w :
    toSL3 w = ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by decide⟩ := by
  show toSL3 (x 0 1 * x 2 (-1) * x 0 1) = _
  rw [map_mul, map_mul, toSL3_x, toSL3_x, elem0_zpow, elem2_zpow]
  apply Subtype.ext
  decide

theorem act_w (v : Fin 3 → ℤ) :
    act (toSL3 w) v = ![v 1, -(v 0), v 2] := by
  refine vec3_ext ?_ ?_ ?_ <;> simp [toSL3_w, act_apply]

/-- Inverse actions of the three signed swaps. -/
theorem act_w_inv (v : Fin 3 → ℤ) :
    act ((toSL3 w)⁻¹) v = ![-(v 1), v 0, v 2] := by
  have h : act (toSL3 w) ![-(v 1), v 0, v 2] = v := by
    rw [act_w]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act ((toSL3 w)⁻¹) v
      = act ((toSL3 w)⁻¹) (act (toSL3 w) ![-(v 1), v 0, v 2]) := by
        rw [h]
    _ = ![-(v 1), v 0, v 2] := by
        rw [← act_mul, inv_mul_cancel, act_one]

theorem act_w13_inv (v : Fin 3 → ℤ) :
    act ((toSL3 w13)⁻¹) v = ![-(v 2), v 1, v 0] := by
  have h : act (toSL3 w13) ![-(v 2), v 1, v 0] = v := by
    rw [act_w13]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act ((toSL3 w13)⁻¹) v
      = act ((toSL3 w13)⁻¹) (act (toSL3 w13) ![-(v 2), v 1, v 0]) := by
        rw [h]
    _ = ![-(v 2), v 1, v 0] := by
        rw [← act_mul, inv_mul_cancel, act_one]

theorem act_w23_inv (v : Fin 3 → ℤ) :
    act ((toSL3 w23)⁻¹) v = ![v 0, -(v 2), v 1] := by
  have h : act (toSL3 w23) ![v 0, -(v 2), v 1] = v := by
    rw [act_w23]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act ((toSL3 w23)⁻¹) v
      = act ((toSL3 w23)⁻¹) (act (toSL3 w23) ![v 0, -(v 2), v 1]) := by
        rw [h]
    _ = ![v 0, -(v 2), v 1] := by
        rw [← act_mul, inv_mul_cancel, act_one]

theorem act_wpow_e3 (k : Fin 4) : act (toSL3 (wpow k)) e3 = e3 := by
  have hw : act (toSL3 w) e3 = e3 := by
    rw [act_w]
    refine vec3_ext ?_ ?_ ?_ <;> simp [e3]
  fin_cases k
  · show act (toSL3 (1 : P13)) e3 = e3
    rw [map_one, act_one]
  · exact hw
  · show act (toSL3 (w * w)) e3 = e3
    rw [map_mul, act_mul, hw, hw]
  · show act (toSL3 (w * (w * w))) e3 = e3
    rw [map_mul, map_mul, act_mul, act_mul, hw, hw, hw]

theorem act_repw_e3 (j : Fin 6) :
    act (toSL3 (repw j)) e3 = repVec j := by
  have h13 : ∀ v, act (toSL3 w13) v = ![v 2, v 1, -(v 0)] := act_w13
  have h23 : ∀ v, act (toSL3 w23) v = ![v 0, v 2, -(v 1)] := act_w23
  fin_cases j
  · show act (toSL3 (1 : P13)) e3 = repVec 0
    rw [map_one, act_one]
    rfl
  · show act (toSL3 w13) e3 = repVec 1
    rw [h13]
    refine vec3_ext ?_ ?_ ?_ <;> simp [e3, repVec]
  · show act (toSL3 w23) e3 = repVec 2
    rw [h23]
    refine vec3_ext ?_ ?_ ?_ <;> simp [e3, repVec]
  · show act (toSL3 (w13 * w13)) e3 = repVec 3
    rw [map_mul, act_mul, h13, h13]
    refine vec3_ext ?_ ?_ ?_ <;> simp [e3, repVec]
  · show act (toSL3 (w13 * (w13 * w13))) e3 = repVec 4
    rw [map_mul, map_mul, act_mul, act_mul, h13, h13, h13]
    refine vec3_ext ?_ ?_ ?_ <;> simp [e3, repVec]
  · show act (toSL3 (w23 * (w13 * w13))) e3 = repVec 5
    rw [map_mul, map_mul, act_mul, act_mul, h13, h13, h23]
    refine vec3_ext ?_ ?_ ?_ <;> simp [e3, repVec]

/-! ## The normal form and the endgame -/

private theorem step_w13 (j : Fin 6) (k : Fin 4) :
    ∃ (j' : Fin 6) (k' : Fin 4),
      w13 * (repw j * wpow k) = repw j' * wpow k' := by
  obtain ⟨j', k1, h1⟩ := w13_mul_repw j
  obtain ⟨k', h2⟩ := wpow_mul_exists k1 k
  exact ⟨j', k', by rw [← mul_assoc, h1, mul_assoc, h2]⟩

private theorem step_w23 (j : Fin 6) (k : Fin 4) :
    ∃ (j' : Fin 6) (k' : Fin 4),
      w23 * (repw j * wpow k) = repw j' * wpow k' := by
  obtain ⟨j', k1, h1⟩ := w23_mul_repw j
  obtain ⟨k', h2⟩ := wpow_mul_exists k1 k
  exact ⟨j', k', by rw [← mul_assoc, h1, mul_assoc, h2]⟩

/-- **Normal form.**  Every element of the signed-swap subgroup is a
coset representative times a power of `w`. -/
theorem exists_rep_wpow {g : P13}
    (hg : g ∈ Subgroup.closure ({w13, w23} : Set P13)) :
    ∃ (j : Fin 6) (k : Fin 4), g = repw j * wpow k := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, by show (1 : P13) = 1 * 1; group⟩
  | mul_left s hs y hy ih =>
      obtain ⟨j, k, rfl⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · obtain ⟨j', k', h⟩ := step_w13 j k
        exact ⟨j', k', by rw [← h]⟩
      · obtain ⟨j', k', h⟩ := step_w23 j k
        exact ⟨j', k', by rw [← h]⟩
  | inv_mul_cancel s hs y hy ih =>
      obtain ⟨j, k, rfl⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · -- w13⁻¹ = w13·(w13·w13): three forward steps
        obtain ⟨j1, k1, h1⟩ := step_w13 j k
        obtain ⟨j2, k2, h2⟩ := step_w13 j1 k1
        obtain ⟨j3, k3, h3⟩ := step_w13 j2 k2
        refine ⟨j3, k3, ?_⟩
        calc w13⁻¹ * (repw j * wpow k)
            = w13 * (w13 * (w13 * (repw j * wpow k))) := by
              rw [w13_inv_eq_cube]; group
          _ = w13 * (w13 * (repw j1 * wpow k1)) := by rw [h1]
          _ = w13 * (repw j2 * wpow k2) := by rw [h2]
          _ = repw j3 * wpow k3 := h3
      · obtain ⟨j1, k1, h1⟩ := step_w23 j k
        obtain ⟨j2, k2, h2⟩ := step_w23 j1 k1
        obtain ⟨j3, k3, h3⟩ := step_w23 j2 k2
        refine ⟨j3, k3, ?_⟩
        calc w23⁻¹ * (repw j * wpow k)
            = w23 * (w23 * (w23 * (repw j * wpow k))) := by
              rw [w23_inv_eq_cube]; group
          _ = w23 * (w23 * (repw j1 * wpow k1)) := by rw [h1]
          _ = w23 * (repw j2 * wpow k2) := by rw [h2]
          _ = repw j3 * wpow k3 := h3

/-- **Machine endgame.**  A signed-swap word whose matrix fixes `e₃`
is a power of `w`, hence parabolic. -/
theorem mem_Hpar_of_stab {g : P13}
    (hg : g ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hstab : act (toSL3 g) e3 = e3) : g ∈ Hpar := by
  obtain ⟨j, k, rfl⟩ := exists_rep_wpow hg
  have himg : act (toSL3 (repw j * wpow k)) e3 = repVec j := by
    rw [map_mul, act_mul, act_wpow_e3, act_repw_e3]
  rw [himg] at hstab
  -- the only representative fixing e₃ is the trivial one
  fin_cases j
  · show (1 : P13) * wpow k ∈ Hpar
    rw [one_mul]
    exact wpow_mem_Hpar k
  · exfalso
    have h := congrFun hstab 0
    simp [repVec, e3] at h
  · exfalso
    have h := congrFun hstab 1
    simp [repVec, e3] at h
  · exfalso
    have h := congrFun hstab 2
    simp [repVec, e3] at h
  · exfalso
    have h := congrFun hstab 0
    simp [repVec, e3] at h
  · exfalso
    have h := congrFun hstab 1
    simp [repVec, e3] at h

end

end P13MonomialMachine
end GroupApproximation
