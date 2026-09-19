import GroupApproximation.Monsters.P13MonomialMachine

/-!
# Core infrastructure for the word descent

The kernel-containment argument runs on words: lists of root letters
`x i c`, evaluated in `P13`, acting on integer columns through the
matrix model.  This file builds the shared layer used by the descent:

* words and their evaluation, and the fact that every element of `P13`
  is the value of a word;
* the letter-wise conjugation action of the signed swaps `w, w13, w23`
  on words, with the push-through lemma that moves a swap across a
  word while transforming its letters;
* the suffix trajectory of a word over a base column and its `ℓ¹`
  norms;
* the corner analysis: a letter that preserves a signed basis column
  of norm one either fixes it or has zero exponent — and hence any
  word whose trajectory from a corner keeps norm one consists of
  letters fixing that corner;
* the endgame assembly: a word of `e₃`-fixing letters conjugated by a
  machine element lands in the parabolic subgroup.

The seven local rewrite cases and the terminating measure descent
live in the next file; here everything is elementary.
-/

namespace GroupApproximation
namespace P13DescentCore

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus
open P13ColumnLift P13ParabolicKernel P13MonomialMachine

noncomputable section

/-! ## Words and evaluation -/

/-- A root letter: a generator index and an integer exponent. -/
abbrev Letter := Fin 6 × ℤ

/-- The value of a letter. -/
def letterVal (l : Letter) : P13 := x l.1 l.2

/-- The value of a word. -/
def eval (W : List Letter) : P13 := (W.map letterVal).prod

@[simp] theorem eval_nil : eval [] = 1 := rfl

theorem eval_cons (l : Letter) (W : List Letter) :
    eval (l :: W) = letterVal l * eval W := by
  unfold eval
  rw [List.map_cons, List.prod_cons]

theorem eval_append (V W : List Letter) :
    eval (V ++ W) = eval V * eval W := by
  unfold eval
  rw [List.map_append, List.prod_append]

/-- A word of unit letters: every exponent is `±1`. -/
def UnitWord (W : List Letter) : Prop :=
  ∀ l ∈ W, l.2 = 1 ∨ l.2 = -1

/-- Every element of `P13` is the value of a unit word. -/
theorem exists_word (g : P13) :
    ∃ W : List Letter, eval W = g ∧ UnitWord W := by
  have hg : g ∈ Subgroup.closure
      (Set.range (PresentedGroup.of (rels := p13Relators))) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨[], rfl, fun l hl => absurd hl List.not_mem_nil⟩
  | mul_left s hs y hy ih =>
      obtain ⟨W, rfl, hU⟩ := ih
      rcases hs with ⟨i, rfl⟩
      refine ⟨(i, 1) :: W, ?_, ?_⟩
      · rw [eval_cons]
        show x i 1 * eval W = PresentedGroup.of i * eval W
        rw [x_one]
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Or.inl rfl
        · exact hU l hl
  | inv_mul_cancel s hs y hy ih =>
      obtain ⟨W, rfl, hU⟩ := ih
      rcases hs with ⟨i, rfl⟩
      refine ⟨(i, -1) :: W, ?_, ?_⟩
      · rw [eval_cons]
        show x i (-1) * eval W = (PresentedGroup.of i)⁻¹ * eval W
        rw [x_neg, x_one]
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Or.inr rfl
        · exact hU l hl

/-! ## Letter conjugation by the signed swaps -/

/-- The letter permutation effected by conjugation with `w`. -/
def wConj : Letter → Letter
  | (0, a) => (2, -a)
  | (1, a) => (3, -a)
  | (2, a) => (0, -a)
  | (3, a) => (1, a)
  | (4, a) => (5, -a)
  | (5, a) => (4, a)

/-- The letter permutation effected by conjugation with `w13`. -/
def w13Conj : Letter → Letter
  | (0, a) => (5, -a)
  | (1, a) => (4, -a)
  | (2, a) => (3, -a)
  | (3, a) => (2, a)
  | (4, a) => (1, -a)
  | (5, a) => (0, a)

/-- The letter permutation effected by conjugation with `w23`. -/
def w23Conj : Letter → Letter
  | (0, a) => (1, -a)
  | (1, a) => (0, a)
  | (2, a) => (4, -a)
  | (3, a) => (5, -a)
  | (4, a) => (2, a)
  | (5, a) => (3, -a)

theorem w_conj_letter (l : Letter) :
    w * letterVal l * w⁻¹ = letterVal (wConj l) := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact w_conj_12 a
  · exact w_conj_13 a
  · exact w_conj_21 a
  · exact w_conj_23 a
  · exact w_conj_31 a
  · exact w_conj_32 a

theorem w13_conj_letter (l : Letter) :
    w13 * letterVal l * w13⁻¹ = letterVal (w13Conj l) := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact w13_conj_12 a
  · exact w13_conj_13 a
  · exact w13_conj_21 a
  · exact w13_conj_23 a
  · exact w13_conj_31 a
  · exact w13_conj_32 a

theorem w23_conj_letter (l : Letter) :
    w23 * letterVal l * w23⁻¹ = letterVal (w23Conj l) := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact w23_conj_12 a
  · exact w23_conj_13 a
  · exact w23_conj_21 a
  · exact w23_conj_23 a
  · exact w23_conj_31 a
  · exact w23_conj_32 a

/-- Pushing an element across a word by letter-wise conjugation. -/
theorem push_through (m : P13) (f : Letter → Letter)
    (hf : ∀ l, m * letterVal l * m⁻¹ = letterVal (f l))
    (W : List Letter) : m * eval W = eval (W.map f) * m := by
  induction W with
  | nil => simp
  | cons l W ih =>
      rw [eval_cons, List.map_cons, eval_cons]
      calc m * (letterVal l * eval W)
          = (m * letterVal l * m⁻¹) * (m * eval W) := by group
        _ = letterVal (f l) * (m * eval W) := by rw [hf]
        _ = letterVal (f l) * (eval (W.map f) * m) := by rw [ih]
        _ = letterVal (f l) * eval (W.map f) * m := by group

/-! ## The trajectory and its norms -/

/-- The `ℓ¹` norm of an integer column. -/
def vnorm (v : Fin 3 → ℤ) : ℕ :=
  (v 0).natAbs + (v 1).natAbs + (v 2).natAbs

/-- The column reached by a word from a base column. -/
def vecOf (W : List Letter) (b : Fin 3 → ℤ) : Fin 3 → ℤ :=
  act (toSL3 (eval W)) b

@[simp] theorem vecOf_nil (b : Fin 3 → ℤ) : vecOf [] b = b := by
  unfold vecOf
  rw [eval_nil, map_one, act_one]

theorem vecOf_cons (l : Letter) (W : List Letter) (b : Fin 3 → ℤ) :
    vecOf (l :: W) b = act (toSL3 (letterVal l)) (vecOf W b) := by
  unfold vecOf
  rw [eval_cons, map_mul, act_mul]

/-- A word is norm-monotone over a base if no letter decreases the
trajectory norm. -/
def Mono : List Letter → (Fin 3 → ℤ) → Prop
  | [], _ => True
  | l :: W, b => Mono W b ∧
      vnorm (vecOf W b) ≤ vnorm (act (toSL3 (letterVal l)) (vecOf W b))

/-! ## Corners -/

/-- The signed basis columns. -/
def IsCorner (v : Fin 3 → ℤ) : Prop :=
  (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ v = ![ε, 0, 0]) ∨
  (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ v = ![0, ε, 0]) ∨
  (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ v = ![0, 0, ε])

theorem isCorner_repVec (j : Fin 6) : IsCorner (repVec j) := by
  fin_cases j
  · exact Or.inr (Or.inr ⟨1, Or.inl rfl, rfl⟩)
  · exact Or.inl ⟨1, Or.inl rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨1, Or.inl rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨-1, Or.inr rfl, rfl⟩)
  · exact Or.inl ⟨-1, Or.inr rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨-1, Or.inr rfl, rfl⟩)

theorem vnorm_corner {v : Fin 3 → ℤ} (hv : IsCorner v) : vnorm v = 1 := by
  rcases hv with ⟨ε, hε, rfl⟩ | ⟨ε, hε, rfl⟩ | ⟨ε, hε, rfl⟩ <;>
    rcases hε with rfl | rfl <;> simp [vnorm]

/-- **Corner rigidity.**  A letter that keeps the norm of a corner at
one fixes the corner. -/
theorem corner_fix {v : Fin 3 → ℤ} (hv : IsCorner v) (l : Letter)
    (h : vnorm (act (toSL3 (letterVal l)) v) ≤ 1) :
    act (toSL3 (letterVal l)) v = v := by
  obtain ⟨i, c⟩ := l
  have hacts : act (toSL3 (letterVal (i, c))) v =
      ![v 0 + (if i = 0 then c * v 1 else if i = 1 then c * v 2 else 0),
        v 1 + (if i = 2 then c * v 0 else if i = 3 then c * v 2 else 0),
        v 2 + (if i = 4 then c * v 0 else if i = 5 then c * v 1 else 0)]
      := by
    match i with
    | 0 =>
        rw [show letterVal ((0 : Fin 6), c) = x 0 c from rfl, act_x0]
        refine vec3_ext ?_ ?_ ?_ <;> simp
    | 1 =>
        rw [show letterVal ((1 : Fin 6), c) = x 1 c from rfl, act_x1]
        refine vec3_ext ?_ ?_ ?_ <;> simp
    | 2 =>
        rw [show letterVal ((2 : Fin 6), c) = x 2 c from rfl, act_x2]
        refine vec3_ext ?_ ?_ ?_ <;> simp
    | 3 =>
        rw [show letterVal ((3 : Fin 6), c) = x 3 c from rfl, act_x3]
        refine vec3_ext ?_ ?_ ?_ <;> simp
    | 4 =>
        rw [show letterVal ((4 : Fin 6), c) = x 4 c from rfl, act_x4]
        refine vec3_ext ?_ ?_ ?_ <;> simp
    | 5 =>
        rw [show letterVal ((5 : Fin 6), c) = x 5 c from rfl, act_x5]
        refine vec3_ext ?_ ?_ ?_ <;> simp
  rw [hacts] at h ⊢
  rcases hv with ⟨ε, hε, rfl⟩ | ⟨ε, hε, rfl⟩ | ⟨ε, hε, rfl⟩ <;>
    rcases hε with rfl | rfl <;>
    fin_cases i <;>
      (refine vec3_ext ?_ ?_ ?_ <;> simp_all [vnorm])

/-! ## Words of stabilizing letters -/

/-- A letter whose matrix fixes `e₃` is parabolic. -/
theorem letter_mem_Hpar_of_fix {l : Letter}
    (h : act (toSL3 (letterVal l)) e3 = e3) : letterVal l ∈ Hpar := by
  obtain ⟨i, c⟩ := l
  have hmem : ∀ i0 : Fin 6, i0 = 0 ∨ i0 = 2 ∨ i0 = 4 ∨ i0 = 5 →
      x i0 c ∈ Hpar := by
    intro i0 hi0
    have hof : ∀ i1 : Fin 6, (PresentedGroup.of i1 : P13) ∈ parGens →
        x i1 c ∈ Hpar := by
      intro i1 h1
      show (PresentedGroup.of i1 : P13) ^ c ∈ Hpar
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure h1) c
    rcases hi0 with rfl | rfl | rfl | rfl <;>
      exact hof _ (by simp [parGens])
  match i, h with
  | 0, _ => exact hmem 0 (by simp)
  | 1, h =>
      -- e₁₃ moves e₃ unless the exponent vanishes
      have h0 := congrFun h 0
      rw [show letterVal ((1 : Fin 6), c) = x 1 c from rfl, act_x1] at h0
      simp [e3] at h0
      subst h0
      show x 1 0 ∈ Hpar
      rw [x_zero]
      exact Subgroup.one_mem _
  | 2, _ => exact hmem 2 (by simp)
  | 3, h =>
      have h1 := congrFun h 1
      rw [show letterVal ((3 : Fin 6), c) = x 3 c from rfl, act_x3] at h1
      simp [e3] at h1
      subst h1
      show x 3 0 ∈ Hpar
      rw [x_zero]
      exact Subgroup.one_mem _
  | 4, _ => exact hmem 4 (by simp)
  | 5, _ => exact hmem 5 (by simp)

/-- A word all of whose letters fix `e₃` evaluates into the
parabolic subgroup. -/
theorem eval_mem_Hpar_of_all_fix {W : List Letter}
    (h : ∀ l ∈ W, act (toSL3 (letterVal l)) e3 = e3) :
    eval W ∈ Hpar := by
  induction W with
  | nil => exact Subgroup.one_mem _
  | cons l W ih =>
      rw [eval_cons]
      exact Subgroup.mul_mem _
        (letter_mem_Hpar_of_fix (h l (List.mem_cons_self)))
        (ih fun l' hl' => h l' (List.mem_cons_of_mem l hl'))

/-! ## The squeeze -/

/-- The zero column is the only column of norm zero. -/
theorem eq_zero_of_vnorm_zero {v : Fin 3 → ℤ} (h : vnorm v = 0) :
    v = fun _ => 0 := by
  unfold vnorm at h
  refine vec3_ext ?_ ?_ ?_ <;> omega

/-- Images of a nonzero column under the matrix model are nonzero. -/
theorem vnorm_vecOf_pos (W : List Letter) {b : Fin 3 → ℤ}
    (hb1 : vnorm b = 1) : 1 ≤ vnorm (vecOf W b) := by
  by_contra hlt
  push Not at hlt
  have h0 : vnorm (vecOf W b) = 0 := by omega
  have hz : vecOf W b = fun _ => 0 := eq_zero_of_vnorm_zero h0
  have hinv : act ((toSL3 (eval W))⁻¹)
      (act (toSL3 (eval W)) b) = b := by
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [show act (toSL3 (eval W)) b = vecOf W b from rfl, hz] at hinv
  have hzero : act ((toSL3 (eval W))⁻¹) (fun _ => (0 : ℤ)) =
      fun _ => (0 : ℤ) := by
    funext k
    simp [act_apply]
  rw [hzero] at hinv
  rw [← hinv] at hb1
  simp [vnorm] at hb1

/-- **Trajectory squeeze.**  If a word is norm-monotone over a corner
base and its total image of the base is again of norm one, then every
suffix vector equals the base and every letter fixes the base. -/
theorem letters_fix_of_mono {W : List Letter} {b : Fin 3 → ℤ}
    (hb : IsCorner b) (hmono : Mono W b)
    (htop : vnorm (vecOf W b) ≤ 1) :
    vecOf W b = b ∧ ∀ l ∈ W, act (toSL3 (letterVal l)) b = b := by
  induction W with
  | nil => exact ⟨vecOf_nil b, fun l hl => absurd hl List.not_mem_nil⟩
  | cons l W ih =>
      obtain ⟨hmW, hstep⟩ := hmono
      have htopc : vnorm (vecOf (l :: W) b) ≤ 1 := htop
      rw [vecOf_cons] at htopc
      have hWnorm : vnorm (vecOf W b) ≤ 1 := le_trans hstep htopc
      obtain ⟨hWeq, hWfix⟩ := ih hmW hWnorm
      rw [hWeq] at htopc
      have hfix : act (toSL3 (letterVal l)) b = b :=
        corner_fix hb l htopc
      refine ⟨?_, ?_⟩
      · rw [vecOf_cons, hWeq, hfix]
      · intro l' hl'
        rcases List.mem_cons.mp hl' with rfl | hl'
        · exact hfix
        · exact hWfix l' hl'

end

end P13DescentCore
end GroupApproximation
