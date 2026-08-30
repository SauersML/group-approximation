import GroupApproximation.Monsters.P13WordDescent

/-!
# Completeness of the thirteen-relator presentation

The assembly of the completeness programme.  Given the descent normal
form — every word of unit root letters equals a norm-monotone word
times a signed-swap element — the kernel of the matrix model
evaporates: a kernel element is a word whose monotone part has
norm-one trajectory over a corner, so all its letters fix the corner;
conjugating through the monomial tail turns it into a parabolic word,
the tail itself is forced into the parabolic subgroup by the machine
endgame, and the parabolic kernel is trivial.  Together with the
elementary generation of `SL₃(ℤ)` this yields the isomorphism

  `p13CompletenessEquiv : P13 ≃* SL₃(ℤ)`,

the machine-checked form of the classical theorem that the Steinberg
presentation with the fourth-power relator presents `SL₃(ℤ)` — the
`K₂(3, ℤ) = ℤ/2` computation in presentation form.
-/

namespace GroupApproximation
namespace P13Completeness

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus
open P13ColumnLift P13ParabolicKernel P13MonomialMachine
open P13DescentCore P13WordDescent

noncomputable section

/-! ## Letters conjugate across the monomial tail -/

/-- The inverse letter permutation of `w13`. -/
def w13ConjInv : Letter → Letter
  | (0, a) => (5, a)
  | (1, a) => (4, -a)
  | (2, a) => (3, a)
  | (3, a) => (2, -a)
  | (4, a) => (1, -a)
  | (5, a) => (0, -a)

/-- The inverse letter permutation of `w23`. -/
def w23ConjInv : Letter → Letter
  | (0, a) => (1, a)
  | (1, a) => (0, -a)
  | (2, a) => (4, a)
  | (3, a) => (5, -a)
  | (4, a) => (2, -a)
  | (5, a) => (3, -a)

theorem w13_inv_conj_letter (l : Letter) :
    w13⁻¹ * letterVal l * w13 = letterVal (w13ConjInv l) := by
  obtain ⟨i, a⟩ := l
  have key : ∀ l' : Letter, w13⁻¹ * letterVal (w13Conj l') * w13 =
      letterVal l' := by
    intro l'
    calc w13⁻¹ * letterVal (w13Conj l') * w13
        = w13⁻¹ * (w13 * letterVal l' * w13⁻¹) * w13 := by
          rw [w13_conj_letter]
      _ = letterVal l' := by group
  match i with
  | 0 => simpa [w13Conj, w13ConjInv] using key (5, a)
  | 1 => simpa [w13Conj, w13ConjInv] using key (4, -a)
  | 2 => simpa [w13Conj, w13ConjInv] using key (3, a)
  | 3 => simpa [w13Conj, w13ConjInv] using key (2, -a)
  | 4 => simpa [w13Conj, w13ConjInv] using key (1, -a)
  | 5 => simpa [w13Conj, w13ConjInv] using key (0, -a)

theorem w23_inv_conj_letter (l : Letter) :
    w23⁻¹ * letterVal l * w23 = letterVal (w23ConjInv l) := by
  obtain ⟨i, a⟩ := l
  have key : ∀ l' : Letter, w23⁻¹ * letterVal (w23Conj l') * w23 =
      letterVal l' := by
    intro l'
    calc w23⁻¹ * letterVal (w23Conj l') * w23
        = w23⁻¹ * (w23 * letterVal l' * w23⁻¹) * w23 := by
          rw [w23_conj_letter]
      _ = letterVal l' := by group
  match i with
  | 0 => simpa [w23Conj, w23ConjInv] using key (1, a)
  | 1 => simpa [w23Conj, w23ConjInv] using key (0, -a)
  | 2 => simpa [w23Conj, w23ConjInv] using key (4, a)
  | 3 => simpa [w23Conj, w23ConjInv] using key (5, -a)
  | 4 => simpa [w23Conj, w23ConjInv] using key (2, -a)
  | 5 => simpa [w23Conj, w23ConjInv] using key (3, -a)

/-- Conjugation by the inverse of any signed-swap element carries
letters to letters. -/
theorem exists_conj_letter_map {mon : P13}
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13)) :
    ∃ f : Letter → Letter,
      ∀ l, mon⁻¹ * letterVal l * mon = letterVal (f l) := by
  induction hmon using Subgroup.closure_induction_left with
  | one => exact ⟨id, fun l => by simp⟩
  | mul_left s hs y hy ih =>
      obtain ⟨f, hf⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · refine ⟨f ∘ w13ConjInv, fun l => ?_⟩
        calc (w13 * y)⁻¹ * letterVal l * (w13 * y)
            = y⁻¹ * (w13⁻¹ * letterVal l * w13) * y := by group
          _ = y⁻¹ * letterVal (w13ConjInv l) * y := by
              rw [w13_inv_conj_letter]
          _ = letterVal (f (w13ConjInv l)) := hf _
      · refine ⟨f ∘ w23ConjInv, fun l => ?_⟩
        calc (w23 * y)⁻¹ * letterVal l * (w23 * y)
            = y⁻¹ * (w23⁻¹ * letterVal l * w23) * y := by group
          _ = y⁻¹ * letterVal (w23ConjInv l) * y := by
              rw [w23_inv_conj_letter]
          _ = letterVal (f (w23ConjInv l)) := hf _
  | inv_mul_cancel s hs y hy ih =>
      obtain ⟨f, hf⟩ := ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · refine ⟨f ∘ w13Conj, fun l => ?_⟩
        calc (w13⁻¹ * y)⁻¹ * letterVal l * (w13⁻¹ * y)
            = y⁻¹ * (w13 * letterVal l * w13⁻¹) * y := by group
          _ = y⁻¹ * letterVal (w13Conj l) * y := by
              rw [w13_conj_letter]
          _ = letterVal (f (w13Conj l)) := hf _
      · refine ⟨f ∘ w23Conj, fun l => ?_⟩
        calc (w23⁻¹ * y)⁻¹ * letterVal l * (w23⁻¹ * y)
            = y⁻¹ * (w23 * letterVal l * w23⁻¹) * y := by group
          _ = y⁻¹ * letterVal (w23Conj l) * y := by
              rw [w23_conj_letter]
          _ = letterVal (f (w23Conj l)) := hf _

/-! ## The parabolic subgroup fixes the third column -/

theorem act_e3_of_mem_Hpar {h : P13} (hh : h ∈ Hpar) :
    act (toSL3 h) e3 = e3 := by
  induction hh using Subgroup.closure_induction with
  | mem g hgen =>
      simp only [parGens, Set.mem_insert_iff, Set.mem_singleton_iff]
        at hgen
      rcases hgen with rfl | rfl | rfl | rfl
      · rw [show (PresentedGroup.of 0 : P13) = x 0 1 from (x_one 0).symm,
          act_x0]
        refine vec3_ext ?_ ?_ ?_ <;> simp [e3]
      · rw [show (PresentedGroup.of 2 : P13) = x 2 1 from (x_one 2).symm,
          act_x2]
        refine vec3_ext ?_ ?_ ?_ <;> simp [e3]
      · rw [show (PresentedGroup.of 4 : P13) = x 4 1 from (x_one 4).symm,
          act_x4]
        refine vec3_ext ?_ ?_ ?_ <;> simp [e3]
      · rw [show (PresentedGroup.of 5 : P13) = x 5 1 from (x_one 5).symm,
          act_x5]
        refine vec3_ext ?_ ?_ ?_ <;> simp [e3]
  | one =>
      rw [map_one, act_one]
  | mul g h _ _ ihg ihh =>
      rw [map_mul, act_mul, ihh, ihg]
  | inv g _ ihg =>
      rw [map_inv]
      have h2 : act ((toSL3 g)⁻¹) (act (toSL3 g) e3) = e3 := by
        rw [← act_mul, inv_mul_cancel, act_one]
      rwa [ihg] at h2

/-! ## The kernel is trivial -/

/-- The image of `e₃` under a signed-swap element is a corner. -/
theorem isCorner_of_closure {mon : P13}
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13)) :
    IsCorner (act (toSL3 mon) e3) := by
  obtain ⟨j, k, rfl⟩ := exists_rep_wpow hmon
  have h : act (toSL3 (repw j * wpow k)) e3 = repVec j := by
    rw [map_mul, act_mul, act_wpow_e3, act_repw_e3]
  rw [h]
  exact isCorner_repVec j

/-- **Kernel triviality**, given the descent normal form. -/
theorem toSL3_ker_eq_bot
    (descent : ∀ W : List Letter, UnitWord W →
      ∃ (G : List Letter) (mon : P13),
      mon ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      eval W = eval G * mon ∧ Mono G (act (toSL3 mon) e3)) :
    ∀ g : P13, toSL3 g = 1 → g = 1 := by
  intro g hg
  obtain ⟨W, rfl, hUW⟩ := exists_word g
  obtain ⟨G, mon, hmon, hWG, hmono⟩ := descent W hUW
  set b := act (toSL3 mon) e3 with hb
  have hbc : IsCorner b := isCorner_of_closure hmon
  -- the monotone part has norm-one image of the corner
  have htop : vecOf G b = act (toSL3 (eval W)) e3 := by
    unfold vecOf
    rw [hb, hWG, map_mul, act_mul]
  have htop1 : vnorm (vecOf G b) ≤ 1 := by
    rw [htop, hg, act_one]
    simp [vnorm, e3]
  obtain ⟨hGfix, hletters⟩ := letters_fix_of_mono hbc hmono htop1
  -- conjugate the monotone part across the tail
  obtain ⟨f, hf⟩ := exists_conj_letter_map hmon
  have hconj : ∀ T : List Letter, mon⁻¹ * eval T * mon = eval (T.map f) := by
    intro T
    induction T with
    | nil => simp
    | cons l T ih =>
        rw [eval_cons, List.map_cons, eval_cons, ← ih]
        calc mon⁻¹ * (letterVal l * eval T) * mon
            = (mon⁻¹ * letterVal l * mon) *
                (mon⁻¹ * eval T * mon) := by group
          _ = letterVal (f l) * (mon⁻¹ * eval T * mon) := by rw [hf]
  -- the conjugated letters fix e₃, hence the conjugate is parabolic
  have hfix' : ∀ l' ∈ G.map f, act (toSL3 (letterVal l')) e3 = e3 := by
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    have hlv := hf l
    have himg : toSL3 (letterVal (f l)) =
        (toSL3 mon)⁻¹ * toSL3 (letterVal l) * toSL3 mon := by
      rw [← hlv]
      simp [map_mul, map_inv]
    rw [himg, act_mul, act_mul, ← hb]
    rw [hletters l hl]
    rw [show act ((toSL3 mon)⁻¹) b = e3 from by
      rw [hb, ← act_mul, inv_mul_cancel, act_one]]
  have hHpar : eval (G.map f) ∈ Hpar := eval_mem_Hpar_of_all_fix hfix'
  -- reassemble: the word is the tail times a parabolic element
  have hsplit : eval W = mon * eval (G.map f) := by
    rw [hWG, ← hconj G]
    group
  -- the tail's matrix fixes e₃, so the machine places it in Hpar
  have hmonstab : act (toSL3 mon) e3 = e3 := by
    have h1 : toSL3 mon = (toSL3 (eval (G.map f)))⁻¹ := by
      have := congrArg toSL3 hsplit
      rw [hg, map_mul] at this
      calc toSL3 mon
          = toSL3 mon * (toSL3 (eval (G.map f)) *
              (toSL3 (eval (G.map f)))⁻¹) := by group
        _ = (toSL3 mon * toSL3 (eval (G.map f))) *
              (toSL3 (eval (G.map f)))⁻¹ := by group
        _ = 1 * (toSL3 (eval (G.map f)))⁻¹ := by rw [← this]
        _ = (toSL3 (eval (G.map f)))⁻¹ := one_mul _
    rw [h1]
    have h2 := act_e3_of_mem_Hpar hHpar
    have h3 : act ((toSL3 (eval (G.map f)))⁻¹)
        (act (toSL3 (eval (G.map f))) e3) = e3 := by
      rw [← act_mul, inv_mul_cancel, act_one]
    rwa [h2] at h3
  have hmonH : mon ∈ Hpar := mem_Hpar_of_stab hmon hmonstab
  have hWH : eval W ∈ Hpar := by
    rw [hsplit]
    exact Subgroup.mul_mem _ hmonH hHpar
  exact eq_one_of_mem_parabolic_of_map_eq_one hWH hg

end

end P13Completeness
end GroupApproximation
