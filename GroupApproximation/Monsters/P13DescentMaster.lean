import GroupApproximation.Monsters.P13Completeness
import GroupApproximation.Monsters.P13DescentCases

/-!
# The descent master induction and the completeness theorem

Work in progress: the step construction is being assembled from the
class rewrite lemmas; the master induction and the final assembly are
complete.  Nothing here is imported by the library root until the
step lands.
-/

namespace GroupApproximation
namespace P13DescentMaster

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus
open P13ColumnLift P13ParabolicKernel P13MonomialMachine
open P13DescentCore P13WordDescent P13Completeness P13DescentCases

noncomputable section

/-- Trajectory values inside a block, in coordinate form: the norm of
the partial block action on the deep vector. -/
theorem sigma_block (A P C : List Letter) (b : Fin 3 → ℤ) (t : ℕ)
    (ht : t ≤ P.length) :
    sigma (A ++ P ++ C) b (A.length + t) =
      vnorm (act (toSL3 (eval (P.drop t))) (vecOf C b)) := by
  unfold sigma
  have hdrop : (A ++ P ++ C).drop (A.length + t) = P.drop t ++ C := by
    rw [List.append_assoc, Nat.add_comm, ← List.drop_drop,
      List.drop_left]
    exact List.drop_append_of_le_length ht
  rw [hdrop]
  unfold vecOf
  rw [eval_append, map_mul, act_mul]

/-- Splitting a word at a violation position: the two offending
letters between the shallow and deep parts. -/
theorem word_split (V : List Letter) (v : ℕ) (hv : v + 1 < V.length) :
    V = V.take v ++ [V[v], V[v + 1]] ++ V.drop (v + 2) := by
  have h1 : V.drop v = V[v] :: V.drop (v + 1) :=
    List.drop_eq_getElem_cons (by omega)
  have h2 : V.drop (v + 1) = V[v + 1] :: V.drop (v + 2) :=
    List.drop_eq_getElem_cons hv
  calc V = V.take v ++ V.drop v := (List.take_append_drop v V).symm
    _ = V.take v ++ [V[v], V[v + 1]] ++ V.drop (v + 2) := by
        rw [h1, h2]
        simp

/-! ## Bridges at the violation -/

/-- σ at the pair positions, in coordinate form over the deep vector. -/
theorem sigma_pair_coords (A C : List Letter) (p q : Letter)
    (b : Fin 3 → ℤ) :
    sigma (A ++ [p, q] ++ C) b A.length =
        vnorm (act (toSL3 (letterVal p))
          (act (toSL3 (letterVal q)) (vecOf C b))) ∧
      sigma (A ++ [p, q] ++ C) b (A.length + 1) =
        vnorm (act (toSL3 (letterVal q)) (vecOf C b)) ∧
      sigma (A ++ [p, q] ++ C) b (A.length + 2) = vnorm (vecOf C b) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := sigma_block A [p, q] C b 0 (by simp)
    rw [Nat.add_zero] at h
    rw [h]
    show vnorm (act (toSL3 (eval [p, q])) (vecOf C b)) = _
    rw [show eval [p, q] = letterVal p * letterVal q from by
      rw [eval_cons, eval_cons, eval_nil, mul_one]]
    rw [map_mul, act_mul]
  · have h := sigma_block A [p, q] C b 1 (by simp)
    rw [h]
    show vnorm (act (toSL3 (eval [q])) (vecOf C b)) = _
    rw [show eval [q] = letterVal q from by
      rw [eval_cons, eval_nil, mul_one]]
  · have h := sigma_block A [p, q] C b 2 (by simp)
    rw [h]
    show vnorm (act (toSL3 (eval ([] : List Letter))) (vecOf C b)) = _
    rw [eval_nil, map_one, act_one]

/-- The pair below the topmost worst violation exists: a violation
cannot sit against a corner base. -/
theorem viol_succ_lt {V : List Letter} {b : Fin 3 → ℤ} {v : ℕ}
    (hb1 : vnorm b = 1) (hv : Viol V b v) : v + 1 < V.length := by
  obtain ⟨hlen, hlt⟩ := hv
  by_contra h
  push_neg at h
  have h1 : v + 1 = V.length ∨ V.length < v + 1 := by omega
  have hle : V.length ≤ v + 1 := h
  have hs1 : sigma V b (v + 1) = vnorm b := sigma_of_ge V b hle
  have hs0 : 1 ≤ sigma V b v := by
    unfold sigma
    exact vnorm_vecOf_pos _ hb1
  omega

/-- The deeper neighbour of the topmost worst violation does not
exceed the violated height. -/
theorem side_le_of_top {V : List Letter} {b : Fin 3 → ℤ}
    (hex : ∃ j, Viol V b j ∧ sigma V b (j + 1) = lam V b) :
    sigma V b (topViol V b hex + 2) ≤ sigma V b (topViol V b hex + 1) := by
  obtain ⟨hv, htop⟩ := topViol_spec hex
  by_contra h
  push_neg at h
  have hv1 : Viol V b (topViol V b hex + 1) := by
    refine ⟨?_, h⟩
    by_contra hlen
    push_neg at hlen
    have := sigma_of_ge V b hlen
    have h2 : sigma V b (topViol V b hex + 1 + 1) ≤ vnorm b := by
      rw [sigma_of_ge V b (by omega)]
    have h3 : vnorm b ≤ sigma V b (topViol V b hex + 1) := by
      rw [← this]
    omega
  have := le_lam hv1
  rw [htop] at h
  omega

/-! ## Cross-base splice facts -/

/-- Shallow trajectory values agree whenever the deep composites act
identically, even across a base change. -/
theorem sigma_shallow_of_actEq (A C₁ C₂ : List Letter)
    (b₁ b₂ : Fin 3 → ℤ)
    (h : act (toSL3 (eval C₁)) b₁ = act (toSL3 (eval C₂)) b₂)
    (j : ℕ) (hj : j ≤ A.length) :
    sigma (A ++ C₁) b₁ j = sigma (A ++ C₂) b₂ j := by
  unfold sigma
  have hdrop : ∀ (D : List Letter),
      (A ++ D).drop j = A.drop j ++ D := fun D =>
    List.drop_append_of_le_length hj
  rw [hdrop C₁, hdrop C₂]
  unfold vecOf
  rw [eval_append, eval_append, map_mul, map_mul, act_mul, act_mul, h]

/-- Conjugated tails act as the original tail conjugated. -/
theorem vecOf_map_conj (m : P13) (f : Letter → Letter)
    (hf : ∀ l, m * letterVal l * m⁻¹ = letterVal (f l))
    (C : List Letter) (b : Fin 3 → ℤ) :
    vecOf (C.map f) (act (toSL3 m) b) = act (toSL3 m) (vecOf C b) := by
  induction C with
  | nil => simp
  | cons l C ih =>
      rw [List.map_cons, vecOf_cons, vecOf_cons, ih]
      have h : letterVal (f l) * m = m * letterVal l := by
        rw [← hf l]
        group
      calc act (toSL3 (letterVal (f l))) (act (toSL3 m) (vecOf C b))
          = act (toSL3 (letterVal (f l)) * toSL3 m) (vecOf C b) := by
            rw [act_mul]
        _ = act (toSL3 (letterVal (f l) * m)) (vecOf C b) := by
            rw [map_mul]
        _ = act (toSL3 (m * letterVal l)) (vecOf C b) := by rw [h]
        _ = act (toSL3 m) (act (toSL3 (letterVal l)) (vecOf C b)) := by
            rw [map_mul, act_mul]

/-- The inverse letter permutation of `w`. -/
def wConjInv : Letter → Letter
  | (0, a) => (2, -a)
  | (1, a) => (3, a)
  | (2, a) => (0, -a)
  | (3, a) => (1, -a)
  | (4, a) => (5, a)
  | (5, a) => (4, -a)

theorem w_inv_conj_letter (l : Letter) :
    w⁻¹ * letterVal l * w = letterVal (wConjInv l) := by
  obtain ⟨i, a⟩ := l
  have key : ∀ l' : Letter, w⁻¹ * letterVal (wConj l') * w =
      letterVal l' := by
    intro l'
    have h := w_conj_letter l'
    calc w⁻¹ * letterVal (wConj l') * w
        = w⁻¹ * (w * letterVal l' * w⁻¹) * w := by rw [h]
      _ = letterVal l' := by group
  fin_cases i
  · have := key (2, -a)
    simpa [wConj, wConjInv] using this
  · have := key (3, a)
    simpa [wConj, wConjInv] using this
  · have := key (0, -a)
    simpa [wConj, wConjInv] using this
  · have := key (1, -a)
    simpa [wConj, wConjInv] using this
  · have := key (5, a)
    simpa [wConj, wConjInv] using this
  · have := key (4, -a)
    simpa [wConj, wConjInv] using this

/-! ## List evaluation and unit-word helpers -/

private theorem eval_single (l : Letter) : eval [l] = letterVal l := by
  rw [eval_cons, eval_nil, mul_one]

private theorem eval_pair' (l₁ l₂ : Letter) :
    eval [l₁, l₂] = letterVal l₁ * letterVal l₂ := by
  rw [eval_cons, eval_single]

private theorem eval_triple (l₁ l₂ l₃ : Letter) :
    eval [l₁, l₂, l₃] = letterVal l₁ * letterVal l₂ * letterVal l₃ := by
  rw [eval_cons, eval_pair']
  group

private theorem letterVal_mk (i : Fin 6) (c : ℤ) :
    letterVal (i, c) = x i c := rfl

private theorem unit_neg {c : ℤ} (hc : c = 1 ∨ c = -1) :
    -c = 1 ∨ -c = -1 := by omega

private theorem unit_mul {c cp : ℤ} (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) : c * cp = 1 ∨ c * cp = -1 := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;> norm_num

private theorem unitWord_nil : UnitWord ([] : List Letter) :=
  fun l hl => absurd hl (List.not_mem_nil l)

private theorem unitWord_single {l₁ : Letter}
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) : UnitWord [l₁] := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact h₁
  · exact absurd hl (List.not_mem_nil l)

private theorem unitWord_pair {l₁ l₂ : Letter}
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) (h₂ : l₂.2 = 1 ∨ l₂.2 = -1) :
    UnitWord [l₁, l₂] := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact h₁
  · exact unitWord_single h₂ l hl

private theorem unitWord_triple {l₁ l₂ l₃ : Letter}
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) (h₂ : l₂.2 = 1 ∨ l₂.2 = -1)
    (h₃ : l₃.2 = 1 ∨ l₃.2 = -1) : UnitWord [l₁, l₂, l₃] := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact h₁
  · exact unitWord_pair h₂ h₃ l hl

private theorem unitWord_take {V : List Letter} (hU : UnitWord V)
    (n : ℕ) : UnitWord (V.take n) :=
  fun l hl => hU l (List.take_subset n V hl)

private theorem unitWord_drop {V : List Letter} (hU : UnitWord V)
    (n : ℕ) : UnitWord (V.drop n) :=
  fun l hl => hU l (List.drop_subset n V hl)

private theorem unitWord_append {A B : List Letter}
    (hA : UnitWord A) (hB : UnitWord B) : UnitWord (A ++ B) := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact hA l h
  · exact hB l h

private theorem unitWord_map {f : Letter → Letter}
    (hf : ∀ l, (f l).2 = l.2 ∨ (f l).2 = -l.2) {C : List Letter}
    (hC : UnitWord C) : UnitWord (C.map f) := by
  intro l' hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
  rcases hf l with h | h <;> rcases hC l hl with h2 | h2 <;>
    rw [h, h2] <;> norm_num

private theorem wConj_sign (l : Letter) :
    (wConj l).2 = l.2 ∨ (wConj l).2 = -l.2 := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem w13Conj_sign (l : Letter) :
    (w13Conj l).2 = l.2 ∨ (w13Conj l).2 = -l.2 := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem w23Conj_sign (l : Letter) :
    (w23Conj l).2 = l.2 ∨ (w23Conj l).2 = -l.2 := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem wConjInv_sign (l : Letter) :
    (wConjInv l).2 = l.2 ∨ (wConjInv l).2 = -l.2 := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem w13ConjInv_sign (l : Letter) :
    (w13ConjInv l).2 = l.2 ∨ (w13ConjInv l).2 = -l.2 := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

private theorem w23ConjInv_sign (l : Letter) :
    (w23ConjInv l).2 = l.2 ∨ (w23ConjInv l).2 = -l.2 := by
  obtain ⟨i, a⟩ := l
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-! ## Element bridges for the braid words -/

private theorem pi_w_neg : x 0 (-1) * x 2 1 * x 0 (-1) = w⁻¹ :=
  w_inv_word.symm

private theorem pi_w13_neg : x 1 (-1) * x 4 1 * x 1 (-1) = w13⁻¹ :=
  w13_inv_word.symm

private theorem pi_w23_neg : x 3 (-1) * x 5 1 * x 3 (-1) = w23⁻¹ :=
  w23_inv_word.symm

/-- The inverted braid relations, from the displayed ones. -/
private theorem braid_neg :
    x 0 (-1) * x 2 1 * x 0 (-1) = x 2 1 * x 0 (-1) * x 2 1 := by
  have h2 : (x 0 1 * x 2 (-1) * x 0 1)⁻¹ =
      (x 2 (-1) * x 0 1 * x 2 (-1))⁻¹ := by rw [braid]
  calc x 0 (-1) * x 2 1 * x 0 (-1)
      = (x 0 1 * x 2 (-1) * x 0 1)⁻¹ := by simp only [x]; group
    _ = (x 2 (-1) * x 0 1 * x 2 (-1))⁻¹ := h2
    _ = x 2 1 * x 0 (-1) * x 2 1 := by simp only [x]; group

private theorem braid13_neg :
    x 1 (-1) * x 4 1 * x 1 (-1) = x 4 1 * x 1 (-1) * x 4 1 := by
  have h2 : (x 1 1 * x 4 (-1) * x 1 1)⁻¹ =
      (x 4 (-1) * x 1 1 * x 4 (-1))⁻¹ := by rw [braid13]
  calc x 1 (-1) * x 4 1 * x 1 (-1)
      = (x 1 1 * x 4 (-1) * x 1 1)⁻¹ := by simp only [x]; group
    _ = (x 4 (-1) * x 1 1 * x 4 (-1))⁻¹ := h2
    _ = x 4 1 * x 1 (-1) * x 4 1 := by simp only [x]; group

private theorem braid23_neg :
    x 3 (-1) * x 5 1 * x 3 (-1) = x 5 1 * x 3 (-1) * x 5 1 := by
  have h2 : (x 3 1 * x 5 (-1) * x 3 1)⁻¹ =
      (x 5 (-1) * x 3 1 * x 5 (-1))⁻¹ := by rw [braid23]
  calc x 3 (-1) * x 5 1 * x 3 (-1)
      = (x 3 1 * x 5 (-1) * x 3 1)⁻¹ := by simp only [x]; group
    _ = (x 5 (-1) * x 3 1 * x 5 (-1))⁻¹ := h2
    _ = x 5 1 * x 3 (-1) * x 5 1 := by simp only [x]; group

/-- The ν-led braid words are the inverse-signed swaps. -/
private theorem nu_w_pos : x 2 1 * x 0 (-1) * x 2 1 = w⁻¹ := by
  rw [← braid_neg]
  exact pi_w_neg

private theorem nu_w_neg : x 2 (-1) * x 0 1 * x 2 (-1) = w := braid.symm

private theorem nu_w13_pos : x 4 1 * x 1 (-1) * x 4 1 = w13⁻¹ := by
  rw [← braid13_neg]
  exact pi_w13_neg

private theorem nu_w13_neg : x 4 (-1) * x 1 1 * x 4 (-1) = w13 :=
  braid13.symm

private theorem nu_w23_pos : x 5 1 * x 3 (-1) * x 5 1 = w23⁻¹ := by
  rw [← braid23_neg]
  exact pi_w23_neg

private theorem nu_w23_neg : x 5 (-1) * x 3 1 * x 5 (-1) = w23 :=
  braid23.symm

/-! ## Inverse actions of the signed swaps -/

private theorem act_w_inv (v : Fin 3 → ℤ) :
    act (toSL3 w⁻¹) v = ![-(v 1), v 0, v 2] := by
  have h : act (toSL3 w) ![-(v 1), v 0, v 2] = v := by
    rw [act_w]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act (toSL3 w⁻¹) v
      = act (toSL3 w⁻¹) (act (toSL3 w) ![-(v 1), v 0, v 2]) := by
        rw [h]
    _ = ![-(v 1), v 0, v 2] := by
        rw [← act_mul, ← map_mul, inv_mul_cancel, map_one, act_one]

private theorem act_w13_inv (v : Fin 3 → ℤ) :
    act (toSL3 w13⁻¹) v = ![-(v 2), v 1, v 0] := by
  have h : act (toSL3 w13) ![-(v 2), v 1, v 0] = v := by
    rw [act_w13]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act (toSL3 w13⁻¹) v
      = act (toSL3 w13⁻¹) (act (toSL3 w13) ![-(v 2), v 1, v 0]) := by
        rw [h]
    _ = ![-(v 2), v 1, v 0] := by
        rw [← act_mul, ← map_mul, inv_mul_cancel, map_one, act_one]

private theorem act_w23_inv (v : Fin 3 → ℤ) :
    act (toSL3 w23⁻¹) v = ![v 0, -(v 2), v 1] := by
  have h : act (toSL3 w23) ![v 0, -(v 2), v 1] = v := by
    rw [act_w23]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act (toSL3 w23⁻¹) v
      = act (toSL3 w23⁻¹) (act (toSL3 w23) ![v 0, -(v 2), v 1]) := by
        rw [h]
    _ = ![v 0, -(v 2), v 1] := by
        rw [← act_mul, ← map_mul, inv_mul_cancel, map_one, act_one]

/-! ## Closure, conjugation, and norm data for the six swap values -/

private theorem mem_pair_left :
    w13 ∈ ({w13, w23} : Set P13) := Set.mem_insert _ _

private theorem mem_pair_right :
    w23 ∈ ({w13, w23} : Set P13) := Set.mem_insert_of_mem _ rfl

private theorem w13_mem_closure :
    w13 ∈ Subgroup.closure ({w13, w23} : Set P13) :=
  Subgroup.subset_closure mem_pair_left

private theorem w23_mem_closure :
    w23 ∈ Subgroup.closure ({w13, w23} : Set P13) :=
  Subgroup.subset_closure mem_pair_right

private theorem w_mem_closure :
    w ∈ Subgroup.closure ({w13, w23} : Set P13) := by
  rw [← w23_conj_w13]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ w23_mem_closure w13_mem_closure)
    (Subgroup.inv_mem _ w23_mem_closure)

private theorem winv_hf (l : Letter) :
    w⁻¹ * letterVal l * (w⁻¹)⁻¹ = letterVal (wConjInv l) := by
  rw [inv_inv]
  exact w_inv_conj_letter l

private theorem w13inv_hf (l : Letter) :
    w13⁻¹ * letterVal l * (w13⁻¹)⁻¹ = letterVal (w13ConjInv l) := by
  rw [inv_inv]
  exact w13_inv_conj_letter l

private theorem w23inv_hf (l : Letter) :
    w23⁻¹ * letterVal l * (w23⁻¹)⁻¹ = letterVal (w23ConjInv l) := by
  rw [inv_inv]
  exact w23_inv_conj_letter l

private theorem vnorm_act_winv (z : Fin 3 → ℤ) :
    vnorm (act (toSL3 w⁻¹) z) = vnorm z := by
  rw [map_inv]
  exact vnorm_act_inv vnorm_act_w z

private theorem vnorm_act_w13inv (z : Fin 3 → ℤ) :
    vnorm (act (toSL3 w13⁻¹) z) = vnorm z := by
  rw [map_inv]
  exact vnorm_act_inv vnorm_act_w13 z

private theorem vnorm_act_w23inv (z : Fin 3 → ℤ) :
    vnorm (act (toSL3 w23⁻¹) z) = vnorm z := by
  rw [map_inv]
  exact vnorm_act_inv vnorm_act_w23 z

/-! ## Generic braid-b identity -/

private theorem braid_b_generic (π ν : Fin 6) (c : ℤ) :
    x ν c * x π (-c) = x π c * (x π (-c) * x ν c * x π (-c)) := by
  calc x ν c * x π (-c)
      = (x π c * x π (-c)) * x ν c * x π (-c) := by
        rw [x_add, show c + -c = 0 from by ring, x_zero, one_mul]
    _ = x π c * (x π (-c) * x ν c * x π (-c)) := by group

/-! ## Corrected emission existence for the ν-led pairs

For six Steinberg pairs the emission spelling of the case table emits
the ν-led braid word, whose transported base is the inverse-signed
swap action; these variants restate the existence disjunctions with
the matching bases. -/

private theorem exist_st_15' (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 5 cp)) u)) <
      vnorm (act (toSL3 (x 5 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 cp)) u)) :
    (vnorm (act (toSL3 (x 1 c)) u) < vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 5 cp)) (act (toSL3 (x 1 c)) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) ∨
    (vnorm (act (toSL3 (x 1 c)) u) < vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 0 (c * cp))) (act (toSL3 (x 1 c)) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) ∨
    (vnorm (act (toSL3 (x 0 (c * cp))) u) <
        vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 0 (c * cp))) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-cp))) ![u 0, -(cp * u 2), cp * u 1]) <
        vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 5 (-cp)))
          ![u 0, -(cp * u 2), cp * u 1])) <
        vnorm (act (toSL3 (x 5 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x1, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

private theorem exist_st_34' (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 4 cp)) u)) <
      vnorm (act (toSL3 (x 4 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 cp)) u)) :
    (vnorm (act (toSL3 (x 3 c)) u) < vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 4 cp)) (act (toSL3 (x 3 c)) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) ∨
    (vnorm (act (toSL3 (x 3 c)) u) < vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 2 (c * cp))) (act (toSL3 (x 3 c)) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) ∨
    (vnorm (act (toSL3 (x 2 (c * cp))) u) <
        vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 2 (c * cp))) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-cp))) ![-(cp * u 2), u 1, cp * u 0]) <
        vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 3 c)) (act (toSL3 (x 4 (-cp)))
          ![-(cp * u 2), u 1, cp * u 0])) <
        vnorm (act (toSL3 (x 4 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x2, act_x3, act_x4] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

private theorem exist_st_52' (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 2 cp)) u)) <
      vnorm (act (toSL3 (x 2 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 cp)) u)) :
    (vnorm (act (toSL3 (x 5 c)) u) < vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 2 cp)) (act (toSL3 (x 5 c)) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) ∨
    (vnorm (act (toSL3 (x 5 c)) u) < vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 4 (c * cp))) (act (toSL3 (x 5 c)) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) ∨
    (vnorm (act (toSL3 (x 4 (c * cp))) u) <
        vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 4 (c * cp))) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-cp))) ![-(cp * u 1), cp * u 0, u 2]) <
        vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 5 c)) (act (toSL3 (x 2 (-cp)))
          ![-(cp * u 1), cp * u 0, u 2])) <
        vnorm (act (toSL3 (x 2 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x2, act_x4, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

private theorem exist_st_12' (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 2 cp)) u)) <
      vnorm (act (toSL3 (x 2 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 cp)) u)) :
    (vnorm (act (toSL3 (x 1 c)) u) < vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 2 cp)) (act (toSL3 (x 1 c)) u)) <
        vnorm (act (toSL3 (x 2 cp)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-cp))) ![-(cp * u 1), cp * u 0, u 2]) <
        vnorm (act (toSL3 (x 2 cp)) u) ∧
      vnorm (act (toSL3 (x 1 c)) (act (toSL3 (x 2 (-cp)))
          ![-(cp * u 1), cp * u 0, u 2])) <
        vnorm (act (toSL3 (x 2 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x1, act_x2] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

private theorem exist_st_04' (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 4 cp)) u)) <
      vnorm (act (toSL3 (x 4 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 cp)) u)) :
    (vnorm (act (toSL3 (x 0 c)) u) < vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 4 cp)) (act (toSL3 (x 0 c)) u)) <
        vnorm (act (toSL3 (x 4 cp)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-cp))) ![-(cp * u 2), u 1, cp * u 0]) <
        vnorm (act (toSL3 (x 4 cp)) u) ∧
      vnorm (act (toSL3 (x 0 c)) (act (toSL3 (x 4 (-cp)))
          ![-(cp * u 2), u 1, cp * u 0])) <
        vnorm (act (toSL3 (x 4 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x0, act_x4] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

private theorem exist_st_25' (c cp : ℤ) (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 5 cp)) u)) <
      vnorm (act (toSL3 (x 5 cp)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 cp)) u)) :
    (vnorm (act (toSL3 (x 2 c)) u) < vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 5 cp)) (act (toSL3 (x 2 c)) u)) <
        vnorm (act (toSL3 (x 5 cp)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-cp))) ![u 0, -(cp * u 2), cp * u 1]) <
        vnorm (act (toSL3 (x 5 cp)) u) ∧
      vnorm (act (toSL3 (x 2 c)) (act (toSL3 (x 5 (-cp)))
          ![u 0, -(cp * u 2), cp * u 1])) <
        vnorm (act (toSL3 (x 5 cp)) u)) := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;>
    simp only [act_x2, act_x5] at hviol hside ⊢ <;>
    simp [vnorm] at hviol hside ⊢ <;>
    omega

/-! ## The step builders -/

private theorem drop_map' (f : Letter → Letter) :
    ∀ (n : ℕ) (l : List Letter), (l.map f).drop n = (l.drop n).map f := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ n ih =>
      intro l
      cases l with
      | nil => simp
      | cons a l => simpa using ih l

/-- A plain splice at the topmost worst violation: the replacement
block evaluates identically, and its internals cut the peak. -/
private theorem step_plain (V : List Letter) (b : Fin 3 → ℤ)
    (hex : ∃ j, Viol V b j ∧ sigma V b (j + 1) = lam V b)
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V b hex)
    (P' : List Letter) (hlen : P'.length ≤ 3)
    (hid : eval P' = letterVal p * letterVal q)
    (hcut : ∀ t, 0 < t → t < P'.length →
      vnorm (act (toSL3 (eval (P'.drop t))) (vecOf C b)) < lam V b) :
    eval V = eval (A ++ P' ++ C) ∧
    Prod.Lex (· < ·) (· < ·) (meas (A ++ P' ++ C) b) (meas V b) := by
  have hVlen : V.length = A.length + 2 + C.length := by
    rw [hsplit]
    simp [List.length_append]
  have hEpair : eval ([p, q] ++ C) = eval (P' ++ C) := by
    rw [eval_append, eval_append, eval_pair', hid]
  have heval : eval V = eval (A ++ P' ++ C) := by
    calc eval V = eval (A ++ [p, q] ++ C) := by rw [hsplit]
      _ = eval A * eval ([p, q] ++ C) := by
          rw [List.append_assoc, eval_append]
      _ = eval A * eval (P' ++ C) := by rw [hEpair]
      _ = eval (A ++ P' ++ C) := by
          rw [List.append_assoc, eval_append]
  refine ⟨heval, ?_⟩
  have D : SpliceData V b :=
    ⟨hex, A, P', C, b, by omega, hAlen, hlen, by omega⟩
  have F : SpliceFacts V b D := by
    refine ⟨?_, ?_, ?_⟩
    · -- shallow
      intro j hj
      show sigma (A ++ P' ++ C) b j = sigma V b j
      have h1 : sigma (A ++ (P' ++ C)) b j =
          sigma (A ++ ([p, q] ++ C)) b j :=
        sigma_shallow_of_actEq A (P' ++ C) ([p, q] ++ C) b b
          (by rw [hEpair]) j hj
      calc sigma (A ++ P' ++ C) b j
          = sigma (A ++ (P' ++ C)) b j := by rw [List.append_assoc]
        _ = sigma (A ++ ([p, q] ++ C)) b j := h1
        _ = sigma (A ++ [p, q] ++ C) b j := by rw [← List.append_assoc]
        _ = sigma V b j := by rw [← hsplit]
    · -- deep
      intro t
      show sigma (A ++ P' ++ C) b (A.length + P'.length + t) =
        sigma V b (A.length + 2 + t)
      have hL := sigma_append_deep (A ++ P') C b t
      rw [List.length_append] at hL
      have hR := sigma_append_deep (A ++ [p, q]) C b t
      rw [List.length_append] at hR
      have hR2 : sigma V b (A.length + 2 + t) = sigma C b t := by
        conv_lhs => rw [hsplit]
        simpa using hR
      rw [hR2]
      exact hL
    · -- cut
      intro t ht0 htl
      show sigma (A ++ P' ++ C) b (A.length + t) < lam V b
      rw [sigma_block A P' C b t (le_of_lt htl)]
      exact hcut t ht0 htl
  exact meas_lt_of_splice V b D F

/-- An emitting splice: the replacement block times the emitted swap
evaluates to the pair, the tail is conjugated across, and the block
internals cut the peak over the transported base. -/
private theorem step_emit (V : List Letter) (b : Fin 3 → ℤ)
    (hex : ∃ j, Viol V b j ∧ sigma V b (j + 1) = lam V b)
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V b hex)
    (P' : List Letter) (hlen : P'.length ≤ 3)
    (wv : P13) (f : Letter → Letter)
    (hf : ∀ l, wv * letterVal l * wv⁻¹ = letterVal (f l))
    (hnorm : ∀ z, vnorm (act (toSL3 wv) z) = vnorm z)
    (hid : eval P' * wv = letterVal p * letterVal q)
    (hcut : ∀ t, 0 < t → t < P'.length →
      vnorm (act (toSL3 (eval (P'.drop t)))
        (act (toSL3 wv) (vecOf C b))) < lam V b) :
    eval V = eval (A ++ P' ++ C.map f) * wv ∧
    Prod.Lex (· < ·) (· < ·)
      (meas (A ++ P' ++ C.map f) (act (toSL3 wv) b)) (meas V b) := by
  have hVlen : V.length = A.length + 2 + C.length := by
    rw [hsplit]
    simp [List.length_append]
  have hpush := push_through wv f hf C
  have heval : eval V = eval (A ++ P' ++ C.map f) * wv := by
    calc eval V = eval A * (letterVal p * letterVal q) * eval C := by
          rw [hsplit, List.append_assoc, eval_append, eval_append,
            eval_pair']
          group
      _ = eval A * (eval P' * wv) * eval C := by rw [hid]
      _ = eval A * eval P' * (wv * eval C) := by group
      _ = eval A * eval P' * (eval (C.map f) * wv) := by rw [hpush]
      _ = (eval A * eval P' * eval (C.map f)) * wv := by group
      _ = eval (A ++ P' ++ C.map f) * wv := by
          rw [eval_append, eval_append]
  refine ⟨heval, ?_⟩
  have hE2 : eval (P' ++ C.map f) * wv = eval ([p, q] ++ C) := by
    rw [eval_append, eval_append, eval_pair']
    calc eval P' * eval (C.map f) * wv
        = eval P' * (eval (C.map f) * wv) := by group
      _ = eval P' * (wv * eval C) := by rw [← hpush]
      _ = (eval P' * wv) * eval C := by group
      _ = letterVal p * letterVal q * eval C := by rw [hid]
  have D : SpliceData V b :=
    ⟨hex, A, P', C.map f, act (toSL3 wv) b, by omega, hAlen, hlen, by
      rw [List.length_map]; omega⟩
  have F : SpliceFacts V b D := by
    refine ⟨?_, ?_, ?_⟩
    · -- shallow
      intro j hj
      show sigma (A ++ P' ++ C.map f) (act (toSL3 wv) b) j =
        sigma V b j
      have hAct : act (toSL3 (eval (P' ++ C.map f)))
          (act (toSL3 wv) b) = act (toSL3 (eval ([p, q] ++ C))) b := by
        have hM : toSL3 (eval (P' ++ C.map f)) * toSL3 wv =
            toSL3 (eval ([p, q] ++ C)) := by
          rw [← map_mul, hE2]
        calc act (toSL3 (eval (P' ++ C.map f))) (act (toSL3 wv) b)
            = act (toSL3 (eval (P' ++ C.map f)) * toSL3 wv) b := by
              rw [act_mul]
          _ = act (toSL3 (eval ([p, q] ++ C))) b := by rw [hM]
      have h1 := sigma_shallow_of_actEq A (P' ++ C.map f)
        ([p, q] ++ C) (act (toSL3 wv) b) b hAct j hj
      calc sigma (A ++ P' ++ C.map f) (act (toSL3 wv) b) j
          = sigma (A ++ (P' ++ C.map f)) (act (toSL3 wv) b) j := by
            rw [List.append_assoc]
        _ = sigma (A ++ ([p, q] ++ C)) b j := h1
        _ = sigma (A ++ [p, q] ++ C) b j := by rw [← List.append_assoc]
        _ = sigma V b j := by rw [← hsplit]
    · -- deep
      intro t
      show sigma (A ++ P' ++ C.map f) (act (toSL3 wv) b)
          (A.length + P'.length + t) = sigma V b (A.length + 2 + t)
      have hL := sigma_append_deep (A ++ P') (C.map f)
        (act (toSL3 wv) b) t
      rw [List.length_append] at hL
      have hmap : sigma (C.map f) (act (toSL3 wv) b) t =
          sigma C b t := by
        unfold sigma
        rw [drop_map', vecOf_map_conj wv f hf, hnorm]
      have hR := sigma_append_deep (A ++ [p, q]) C b t
      rw [List.length_append] at hR
      have hR2 : sigma V b (A.length + 2 + t) = sigma C b t := by
        conv_lhs => rw [hsplit]
        simpa using hR
      rw [hR2, ← hmap]
      exact hL
    · -- cut
      intro t ht0 htl
      show sigma (A ++ P' ++ C.map f) (act (toSL3 wv) b)
          (A.length + t) < lam V b
      rw [sigma_block A P' (C.map f) (act (toSL3 wv) b) t
        (le_of_lt htl)]
      rw [vecOf_map_conj wv f hf]
      exact hcut t ht0 htl
  exact meas_lt_of_splice V b D F

/-- **One descent step.**  A word with a violation rewrites, up to a
signed-swap element pushed rightward, into a configuration of strictly
smaller measure. -/
theorem descent_step (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hviol : ∃ j, Viol V (act (toSL3 mon) e3) j) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  sorry

/-- **The descent normal form.**  Every word equals a norm-monotone
word times a signed-swap element. -/
theorem descent_normal_form (W : List Letter) (hUW : UnitWord W) :
    ∃ (G : List Letter) (mon : P13),
      mon ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      eval W = eval G * mon ∧ Mono G (act (toSL3 mon) e3) := by
  suffices H : ∀ p : ℕ × ℕ, ∀ (V : List Letter) (mon : P13),
      mon ∈ Subgroup.closure ({w13, w23} : Set P13) →
      UnitWord V →
      meas V (act (toSL3 mon) e3) = p →
      ∃ (G : List Letter) (mon' : P13),
        mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
        eval V * mon = eval G * mon' ∧
        Mono G (act (toSL3 mon') e3) by
    obtain ⟨G, mon', h1, h2, h3⟩ :=
      H (meas W (act (toSL3 1) e3)) W 1 (Subgroup.one_mem _) hUW rfl
    exact ⟨G, mon', h1, by simpa using h2, h3⟩
  intro p
  induction p using
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf).induction
    with
  | _ p IH =>
      intro V mon hmon hUV hp
      by_cases hv : ∃ j, Viol V (act (toSL3 mon) e3) j
      · obtain ⟨V', mon', hmon', hUV', heval, hlt⟩ :=
          descent_step V mon hmon hUV hv
        rw [hp] at hlt
        obtain ⟨G, mon'', h1, h2, h3⟩ :=
          IH _ hlt V' mon' hmon' hUV' rfl
        refine ⟨G, mon'', h1, ?_, h3⟩
        rw [← h2, heval]
      · push_neg at hv
        exact ⟨V, mon, hmon, rfl,
          (mono_iff_no_viol V _).mpr fun j hj => hv j hj⟩

/-- **Injectivity of the matrix model.** -/
theorem toSL3_injective : Function.Injective toSL3 := by
  rw [injective_iff_map_eq_one]
  exact toSL3_ker_eq_bot descent_normal_form

/-- **Completeness of the thirteen-relator presentation:** the
canonical homomorphism is an isomorphism `P13 ≃* SL₃(ℤ)`. -/
noncomputable def p13CompletenessEquiv : P13 ≃* SL3 :=
  MulEquiv.ofBijective toSL3
    ⟨toSL3_injective, SL3ElementaryGeneration.toSL3_surjective⟩

end

end P13DescentMaster
end GroupApproximation
