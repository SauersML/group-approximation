import GroupApproximation.Monsters.P13Completeness
import GroupApproximation.Monsters.P13DescentCases

/-!
# The descent master induction and the completeness theorem

The last file of the completeness programme, and the one carrying the
badge for Theorem `thm:p13-complete`.  Everything the descent needs is
already in place — the trajectory measure and the splice principle
(`P13WordDescent`), the class-by-class rewrite catalog
(`P13DescentCases`), the corner analysis and the endgame assembly
(`P13DescentCore`), the parabolic separation (`P13ParabolicKernel`),
the six-coset Schreier normal form (`P13MonomialMachine`) and the
kernel assembly (`P13Completeness`) — and this file runs it:

* the bridges at the violation, which read the trajectory norms at the
  two offending positions off the coordinate action, and the routes
  that discharge a rewrite once its identity and existence lemmas are
  supplied;
* `descent_step`: a word with a violation rewrites, up to a signed-swap
  element pushed rightward, into a configuration of strictly smaller
  measure.  The proof splits the word at the topmost worst violation
  and exhausts all thirty-six ordered pairs of letter families,
  `(0,0)` through `(5,5)`, with no catch-all branch;
* `descent_normal_form`: the master induction, a well-founded descent
  on `Prod.Lex` over the pair `(lam, length − topViol)`, one
  `descent_step` per round, terminating exactly when no violation
  remains.  Every word of unit root letters equals a norm-monotone
  word times an element of the signed-swap subgroup `⟨w13, w23⟩`;
* `toSL3_injective`, by feeding that normal form to
  `P13Completeness.toSL3_ker_eq_bot`, and then
  `p13CompletenessEquiv : P13 ≃* SL₃(ℤ)`, injectivity together with
  the elementary generation of `SL₃(ℤ)`.

A namespace clash is inherited from the `open` list: `sigma` names both
the trajectory norm (`P13WordDescent.sigma`, `ℕ`-valued) and the
transversal cocycle of the unused lift route (`P13ColumnLift.sigma`,
`P13`-valued).  Proofs here mean the former and say so explicitly
(`unfold P13WordDescent.sigma`).
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
  unfold P13WordDescent.sigma
  have hdrop : (A ++ P ++ C).drop (A.length + t) = P.drop t ++ C := by
    rw [List.append_assoc, ← List.drop_drop, List.drop_left]
    exact List.drop_append_of_le_length ht
  rw [hdrop]
  unfold vecOf
  rw [eval_append, map_mul, act_mul]

/-- Splitting a word at a violation position: the two offending
letters between the shallow and deep parts. -/
theorem word_split (V : List Letter) (v : ℕ) (hv : v + 1 < V.length) :
    V = V.take v ++ [V[v], V[v + 1]] ++ V.drop (v + 2) := by
  calc V = V.take v ++ V.drop v := (List.take_append_drop v V).symm
    _ = V.take v ++ [V[v], V[v + 1]] ++ V.drop (v + 2) := by
        rw [List.drop_eq_getElem_cons (by lia), List.drop_eq_getElem_cons hv]
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
  push Not at h
  have h1 : v + 1 = V.length ∨ V.length < v + 1 := by lia
  have hle : V.length ≤ v + 1 := h
  have hs1 : sigma V b (v + 1) = vnorm b := sigma_of_ge V b hle
  have hs0 : 1 ≤ sigma V b v := by
    unfold P13WordDescent.sigma
    exact vnorm_vecOf_pos _ hb1
  lia

/-- The deeper neighbour of the topmost worst violation does not
exceed the violated height. -/
theorem side_le_of_top {V : List Letter} {b : Fin 3 → ℤ}
    (hex : ∃ j, Viol V b j ∧ sigma V b (j + 1) = lam V b) :
    sigma V b (topViol V b hex + 2) ≤ sigma V b (topViol V b hex + 1) := by
  obtain ⟨hv, htop⟩ := topViol_spec hex
  by_contra h
  push Not at h
  have hv1 : Viol V b (topViol V b hex + 1) := by
    refine ⟨?_, h⟩
    by_contra hlen
    push Not at hlen
    have := sigma_of_ge V b hlen
    have h2 : sigma V b (topViol V b hex + 2) ≤ vnorm b := by
      rw [sigma_of_ge V b (by lia)]
    have h3 : vnorm b ≤ sigma V b (topViol V b hex + 1) := by
      rw [← this]
    lia
  have hlam := le_lam hv1
  rw [show topViol V b hex + 1 + 1 = topViol V b hex + 2 from rfl] at hlam
  rw [htop] at h
  lia

/-! ## Cross-base splice facts -/

/-- Shallow trajectory values agree whenever the deep composites act
identically, even across a base change. -/
theorem sigma_shallow_of_actEq (A C₁ C₂ : List Letter)
    (b₁ b₂ : Fin 3 → ℤ)
    (h : act (toSL3 (eval C₁)) b₁ = act (toSL3 (eval C₂)) b₂)
    (j : ℕ) (hj : j ≤ A.length) :
    sigma (A ++ C₁) b₁ j = sigma (A ++ C₂) b₂ j := by
  unfold P13WordDescent.sigma
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
    calc w⁻¹ * letterVal (wConj l') * w
        = w⁻¹ * (w * letterVal l' * w⁻¹) * w := by rw [w_conj_letter]
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

private theorem unit_neg {c : ℤ} (hc : c = 1 ∨ c = -1) :
    -c = 1 ∨ -c = -1 := by lia

private theorem unit_mul {c cp : ℤ} (hc : c = 1 ∨ c = -1)
    (hcp : cp = 1 ∨ cp = -1) : c * cp = 1 ∨ c * cp = -1 := by
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl <;> norm_num

private theorem unitWord_nil : UnitWord ([] : List Letter) :=
  fun _l hl => absurd hl List.not_mem_nil

private theorem unitWord_single {l₁ : Letter}
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) : UnitWord [l₁] := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact h₁
  · exact absurd hl List.not_mem_nil

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

/-- The positive-led braid words are the swaps, definitionally. -/
@[simp] private theorem pi_w_pos : x 0 1 * x 2 (-1) * x 0 1 = w := rfl

@[simp] private theorem pi_w13_pos : x 1 1 * x 4 (-1) * x 1 1 = w13 := rfl

@[simp] private theorem pi_w23_pos : x 3 1 * x 5 (-1) * x 3 1 = w23 := rfl

/-- The inverted braid relations, from the displayed ones. -/
private theorem braid_neg :
    x 0 (-1) * x 2 1 * x 0 (-1) = x 2 1 * x 0 (-1) * x 2 1 := by
  calc x 0 (-1) * x 2 1 * x 0 (-1)
      = (x 0 1 * x 2 (-1) * x 0 1)⁻¹ := by simp only [x]; group
    _ = (x 2 (-1) * x 0 1 * x 2 (-1))⁻¹ := by rw [braid]
    _ = x 2 1 * x 0 (-1) * x 2 1 := by simp only [x]; group

private theorem braid13_neg :
    x 1 (-1) * x 4 1 * x 1 (-1) = x 4 1 * x 1 (-1) * x 4 1 := by
  calc x 1 (-1) * x 4 1 * x 1 (-1)
      = (x 1 1 * x 4 (-1) * x 1 1)⁻¹ := by simp only [x]; group
    _ = (x 4 (-1) * x 1 1 * x 4 (-1))⁻¹ := by rw [braid13]
    _ = x 4 1 * x 1 (-1) * x 4 1 := by simp only [x]; group

private theorem braid23_neg :
    x 3 (-1) * x 5 1 * x 3 (-1) = x 5 1 * x 3 (-1) * x 5 1 := by
  calc x 3 (-1) * x 5 1 * x 3 (-1)
      = (x 3 1 * x 5 (-1) * x 3 1)⁻¹ := by simp only [x]; group
    _ = (x 5 (-1) * x 3 1 * x 5 (-1))⁻¹ := by rw [braid23]
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

/-- Reversed-pair emission identity for the pair `(x3, x0)`. -/
private theorem emR_30 (c cp : ℤ) (hc : c = 1 ∨ c = -1) :
    x 5 c * x 1 (-(c * cp)) * x 3 (-c) *
      (x 3 c * x 5 (-c) * x 3 c) = x 3 c * x 0 cp := by
  have hc2 : -(c * -(c * cp)) = cp := by rcases hc with rfl | rfl <;> ring
  calc x 5 c * x 1 (-(c * cp)) * x 3 (-c) *
        (x 3 c * x 5 (-c) * x 3 c)
      = x 5 c * x 1 (-(c * cp)) * (x 3 (-c) * x 3 c) *
          (x 5 (-c) * x 3 c) := by group
    _ = x 5 c * x 1 (-(c * cp)) * (x 5 (-c) * x 3 c) := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]
    _ = x 5 c * x 1 (-(c * cp)) * x 5 (-c) * x 3 c := by group
    _ = x 0 (-(c * -(c * cp))) * x 1 (-(c * cp)) * x 3 c := by
        rw [sand5_conj]
    _ = x 0 cp * x 1 (-(c * cp)) * x 3 c := by rw [hc2]
    _ = x 1 (-(c * cp)) * x 0 cp * x 3 c := by
        rw [(x_commute_12_13 cp (-(c * cp))).eq]
    _ = x 3 c * x 0 cp * x 3 (-c) * x 3 c := by rw [← sand3_conj]
    _ = x 3 c * x 0 cp * (x 3 (-c) * x 3 c) := by group
    _ = x 3 c * x 0 cp := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]

/-- Reversed-pair emission identity for the pair `(x5, x1)`. -/
private theorem emR_51 (c cp : ℤ) (hc : c = 1 ∨ c = -1) :
    x 3 c * x 0 (-(c * cp)) * x 5 (-c) *
      (x 5 c * x 3 (-c) * x 5 c) = x 5 c * x 1 cp := by
  have hc2 : -(c * -(c * cp)) = cp := by rcases hc with rfl | rfl <;> ring
  calc x 3 c * x 0 (-(c * cp)) * x 5 (-c) *
        (x 5 c * x 3 (-c) * x 5 c)
      = x 3 c * x 0 (-(c * cp)) * (x 5 (-c) * x 5 c) *
          (x 3 (-c) * x 5 c) := by group
    _ = x 3 c * x 0 (-(c * cp)) * (x 3 (-c) * x 5 c) := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]
    _ = x 3 c * x 0 (-(c * cp)) * x 3 (-c) * x 5 c := by group
    _ = x 1 (-(c * -(c * cp))) * x 0 (-(c * cp)) * x 5 c := by
        rw [sand3_conj]
    _ = x 1 cp * x 0 (-(c * cp)) * x 5 c := by rw [hc2]
    _ = x 0 (-(c * cp)) * x 1 cp * x 5 c := by
        rw [((x_commute_12_13 (-(c * cp)) cp).symm).eq]
    _ = x 5 c * x 1 cp * x 5 (-c) * x 5 c := by rw [← sand5_conj]
    _ = x 5 c * x 1 cp * (x 5 (-c) * x 5 c) := by group
    _ = x 5 c * x 1 cp := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]

/-- Reversed-pair emission identity for the pair `(x1, x2)`. -/
private theorem emR_12 (c cp : ℤ) (hc : c = 1 ∨ c = -1) :
    x 4 c * x 3 (-(c * cp)) * x 1 (-c) *
      (x 1 c * x 4 (-c) * x 1 c) = x 1 c * x 2 cp := by
  have hc2 : -(c * -(c * cp)) = cp := by rcases hc with rfl | rfl <;> ring
  calc x 4 c * x 3 (-(c * cp)) * x 1 (-c) *
        (x 1 c * x 4 (-c) * x 1 c)
      = x 4 c * x 3 (-(c * cp)) * (x 1 (-c) * x 1 c) *
          (x 4 (-c) * x 1 c) := by group
    _ = x 4 c * x 3 (-(c * cp)) * (x 4 (-c) * x 1 c) := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]
    _ = x 4 c * x 3 (-(c * cp)) * x 4 (-c) * x 1 c := by group
    _ = x 2 (-(c * -(c * cp))) * x 3 (-(c * cp)) * x 1 c := by
        rw [sand4_conj]
    _ = x 2 cp * x 3 (-(c * cp)) * x 1 c := by rw [hc2]
    _ = x 3 (-(c * cp)) * x 2 cp * x 1 c := by
        rw [(x_commute_21_23 cp (-(c * cp))).eq]
    _ = x 1 c * x 2 cp * x 1 (-c) * x 1 c := by rw [← sand1_conj]
    _ = x 1 c * x 2 cp * (x 1 (-c) * x 1 c) := by group
    _ = x 1 c * x 2 cp := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]

/-- Reversed-pair emission identity for the pair `(x4, x3)`. -/
private theorem emR_43 (c cp : ℤ) (hc : c = 1 ∨ c = -1) :
    x 1 c * x 2 (-(c * cp)) * x 4 (-c) *
      (x 4 c * x 1 (-c) * x 4 c) = x 4 c * x 3 cp := by
  have hc2 : -(c * -(c * cp)) = cp := by rcases hc with rfl | rfl <;> ring
  calc x 1 c * x 2 (-(c * cp)) * x 4 (-c) *
        (x 4 c * x 1 (-c) * x 4 c)
      = x 1 c * x 2 (-(c * cp)) * (x 4 (-c) * x 4 c) *
          (x 1 (-c) * x 4 c) := by group
    _ = x 1 c * x 2 (-(c * cp)) * (x 1 (-c) * x 4 c) := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]
    _ = x 1 c * x 2 (-(c * cp)) * x 1 (-c) * x 4 c := by group
    _ = x 3 (-(c * -(c * cp))) * x 2 (-(c * cp)) * x 4 c := by
        rw [sand1_conj]
    _ = x 3 cp * x 2 (-(c * cp)) * x 4 c := by rw [hc2]
    _ = x 2 (-(c * cp)) * x 3 cp * x 4 c := by
        rw [((x_commute_21_23 (-(c * cp)) cp).symm).eq]
    _ = x 4 c * x 3 cp * x 4 (-c) * x 4 c := by rw [← sand4_conj]
    _ = x 4 c * x 3 cp * (x 4 (-c) * x 4 c) := by group
    _ = x 4 c * x 3 cp := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]

/-- Reversed-pair emission identity for the pair `(x0, x4)`. -/
private theorem emR_04 (c cp : ℤ) (hc : c = 1 ∨ c = -1) :
    x 2 c * x 5 (-(c * cp)) * x 0 (-c) *
      (x 0 c * x 2 (-c) * x 0 c) = x 0 c * x 4 cp := by
  have hc2 : -(c * -(c * cp)) = cp := by rcases hc with rfl | rfl <;> ring
  calc x 2 c * x 5 (-(c * cp)) * x 0 (-c) *
        (x 0 c * x 2 (-c) * x 0 c)
      = x 2 c * x 5 (-(c * cp)) * (x 0 (-c) * x 0 c) *
          (x 2 (-c) * x 0 c) := by group
    _ = x 2 c * x 5 (-(c * cp)) * (x 2 (-c) * x 0 c) := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]
    _ = x 2 c * x 5 (-(c * cp)) * x 2 (-c) * x 0 c := by group
    _ = x 4 (-(c * -(c * cp))) * x 5 (-(c * cp)) * x 0 c := by
        rw [sand2_conj]
    _ = x 4 cp * x 5 (-(c * cp)) * x 0 c := by rw [hc2]
    _ = x 5 (-(c * cp)) * x 4 cp * x 0 c := by
        rw [(x_commute_31_32 cp (-(c * cp))).eq]
    _ = x 0 c * x 4 cp * x 0 (-c) * x 0 c := by rw [← sand0_conj]
    _ = x 0 c * x 4 cp * (x 0 (-c) * x 0 c) := by group
    _ = x 0 c * x 4 cp := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]

/-- Reversed-pair emission identity for the pair `(x2, x5)`. -/
private theorem emR_25 (c cp : ℤ) (hc : c = 1 ∨ c = -1) :
    x 0 c * x 4 (-(c * cp)) * x 2 (-c) *
      (x 2 c * x 0 (-c) * x 2 c) = x 2 c * x 5 cp := by
  have hc2 : -(c * -(c * cp)) = cp := by rcases hc with rfl | rfl <;> ring
  calc x 0 c * x 4 (-(c * cp)) * x 2 (-c) *
        (x 2 c * x 0 (-c) * x 2 c)
      = x 0 c * x 4 (-(c * cp)) * (x 2 (-c) * x 2 c) *
          (x 0 (-c) * x 2 c) := by group
    _ = x 0 c * x 4 (-(c * cp)) * (x 0 (-c) * x 2 c) := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]
    _ = x 0 c * x 4 (-(c * cp)) * x 0 (-c) * x 2 c := by group
    _ = x 5 (-(c * -(c * cp))) * x 4 (-(c * cp)) * x 2 c := by
        rw [sand0_conj]
    _ = x 5 cp * x 4 (-(c * cp)) * x 2 c := by rw [hc2]
    _ = x 4 (-(c * cp)) * x 5 cp * x 2 c := by
        rw [((x_commute_31_32 (-(c * cp)) cp).symm).eq]
    _ = x 2 c * x 5 cp * x 2 (-c) * x 2 c := by rw [← sand2_conj]
    _ = x 2 c * x 5 cp * (x 2 (-c) * x 2 c) := by group
    _ = x 2 c * x 5 cp := by
        rw [x_add, show -c + c = 0 from by ring, x_zero, mul_one]

/-! ## Inverse actions of the signed swaps -/

private theorem act_winv_vec (v : Fin 3 → ℤ) :
    act (toSL3 w⁻¹) v = ![-(v 1), v 0, v 2] := by
  have h : act (toSL3 w) ![-(v 1), v 0, v 2] = v := by
    rw [act_w]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act (toSL3 w⁻¹) v
      = act (toSL3 w⁻¹) (act (toSL3 w) ![-(v 1), v 0, v 2]) := by
        rw [h]
    _ = ![-(v 1), v 0, v 2] := by
        rw [← act_mul, ← map_mul, inv_mul_cancel, map_one, act_one]

private theorem act_w13inv_vec (v : Fin 3 → ℤ) :
    act (toSL3 w13⁻¹) v = ![-(v 2), v 1, v 0] := by
  have h : act (toSL3 w13) ![-(v 2), v 1, v 0] = v := by
    rw [act_w13]
    refine vec3_ext ?_ ?_ ?_ <;> simp
  calc act (toSL3 w13⁻¹) v
      = act (toSL3 w13⁻¹) (act (toSL3 w13) ![-(v 2), v 1, v 0]) := by
        rw [h]
    _ = ![-(v 2), v 1, v 0] := by
        rw [← act_mul, ← map_mul, inv_mul_cancel, map_one, act_one]

private theorem act_w23inv_vec (v : Fin 3 → ℤ) :
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

/-! ## Corrected emission existence for the ν-led pairs

For six Steinberg pairs the emission spelling of the case table emits
the ν-led braid word, whose transported base is the inverse-signed
swap action; these variants restate the existence disjunctions with
the matching bases. -/

private theorem exist_st_15_pp' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 5 1)) u)) <
      vnorm (act (toSL3 (x 5 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 1)) u)) :
    (vnorm (act (toSL3 (x 1 1)) u) < vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 1 1)) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 1)) u) < vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 0 (1 * 1))) (act (toSL3 (x 1 1)) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 (1 * 1))) u) <
        vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 0 (1 * 1))) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-1))) ![u 0, -(1 * u 2), 1 * u 1]) <
        vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 5 (-1)))
          ![u 0, -(1 * u 2), 1 * u 1])) <
        vnorm (act (toSL3 (x 5 1)) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_15_pm' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 5 (-1))) u)) <
      vnorm (act (toSL3 (x 5 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 (-1))) u)) :
    (vnorm (act (toSL3 (x 1 1)) u) < vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 1 1)) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 1)) u) < vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 (1 * (-1)))) (act (toSL3 (x 1 1)) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 (1 * (-1)))) u) <
        vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 0 (1 * (-1)))) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 (-(-1)))) ![u 0, -((-1) * u 2), (-1) * u 1]) <
        vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 1)) (act (toSL3 (x 5 (-(-1))))
          ![u 0, -((-1) * u 2), (-1) * u 1])) <
        vnorm (act (toSL3 (x 5 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_15_mp' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 5 1)) u)) <
      vnorm (act (toSL3 (x 5 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 1)) u)) :
    (vnorm (act (toSL3 (x 1 (-1))) u) < vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 1 (-1))) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 1 (-1))) u) < vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 0 ((-1) * 1))) (act (toSL3 (x 1 (-1))) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 0 ((-1) * 1))) u) <
        vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 0 ((-1) * 1))) u)) <
        vnorm (act (toSL3 (x 5 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-1))) ![u 0, -(1 * u 2), 1 * u 1]) <
        vnorm (act (toSL3 (x 5 1)) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 5 (-1)))
          ![u 0, -(1 * u 2), 1 * u 1])) <
        vnorm (act (toSL3 (x 5 1)) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_15_mm' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 5 (-1))) u)) <
      vnorm (act (toSL3 (x 5 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 5 (-1))) u)) :
    (vnorm (act (toSL3 (x 1 (-1))) u) < vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 1 (-1))) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 1 (-1))) u) < vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 0 ((-1) * (-1)))) (act (toSL3 (x 1 (-1))) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 0 ((-1) * (-1)))) u) <
        vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 0 ((-1) * (-1)))) u)) <
        vnorm (act (toSL3 (x 5 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 (-(-1)))) ![u 0, -((-1) * u 2), (-1) * u 1]) <
        vnorm (act (toSL3 (x 5 (-1))) u) ∧
      vnorm (act (toSL3 (x 1 (-1))) (act (toSL3 (x 5 (-(-1))))
          ![u 0, -((-1) * u 2), (-1) * u 1])) <
        vnorm (act (toSL3 (x 5 (-1))) u)) := by
  simp only [act_x0, act_x1, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

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
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_15_pp' u hviol hside, exist_st_15_pm' u hviol hside,
    exist_st_15_mp' u hviol hside, exist_st_15_mm' u hviol hside]

private theorem exist_st_34_pp' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 4 1)) u)) <
      vnorm (act (toSL3 (x 4 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 1)) u)) :
    (vnorm (act (toSL3 (x 3 1)) u) < vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 3 1)) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 1)) u) < vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 2 (1 * 1))) (act (toSL3 (x 3 1)) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 (1 * 1))) u) <
        vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 2 (1 * 1))) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-1))) ![-(1 * u 2), u 1, 1 * u 0]) <
        vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 4 (-1)))
          ![-(1 * u 2), u 1, 1 * u 0])) <
        vnorm (act (toSL3 (x 4 1)) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_34_pm' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 4 (-1))) u)) <
      vnorm (act (toSL3 (x 4 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 (-1))) u)) :
    (vnorm (act (toSL3 (x 3 1)) u) < vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 3 1)) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 1)) u) < vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (1 * (-1)))) (act (toSL3 (x 3 1)) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 (1 * (-1)))) u) <
        vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 2 (1 * (-1)))) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 (-(-1)))) ![-((-1) * u 2), u 1, (-1) * u 0]) <
        vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 1)) (act (toSL3 (x 4 (-(-1))))
          ![-((-1) * u 2), u 1, (-1) * u 0])) <
        vnorm (act (toSL3 (x 4 (-1))) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_34_mp' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 4 1)) u)) <
      vnorm (act (toSL3 (x 4 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 1)) u)) :
    (vnorm (act (toSL3 (x 3 (-1))) u) < vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 4 1)) (act (toSL3 (x 3 (-1))) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 3 (-1))) u) < vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 2 ((-1) * 1))) (act (toSL3 (x 3 (-1))) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 ((-1) * 1))) u) <
        vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 2 ((-1) * 1))) u)) <
        vnorm (act (toSL3 (x 4 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 (-1))) ![-(1 * u 2), u 1, 1 * u 0]) <
        vnorm (act (toSL3 (x 4 1)) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 4 (-1)))
          ![-(1 * u 2), u 1, 1 * u 0])) <
        vnorm (act (toSL3 (x 4 1)) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_34_mm' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 4 (-1))) u)) <
      vnorm (act (toSL3 (x 4 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 4 (-1))) u)) :
    (vnorm (act (toSL3 (x 3 (-1))) u) < vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (-1))) (act (toSL3 (x 3 (-1))) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 3 (-1))) u) < vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 ((-1) * (-1)))) (act (toSL3 (x 3 (-1))) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 ((-1) * (-1)))) u) <
        vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 2 ((-1) * (-1)))) u)) <
        vnorm (act (toSL3 (x 4 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 (-(-1)))) ![-((-1) * u 2), u 1, (-1) * u 0]) <
        vnorm (act (toSL3 (x 4 (-1))) u) ∧
      vnorm (act (toSL3 (x 3 (-1))) (act (toSL3 (x 4 (-(-1))))
          ![-((-1) * u 2), u 1, (-1) * u 0])) <
        vnorm (act (toSL3 (x 4 (-1))) u)) := by
  simp only [act_x2, act_x3, act_x4, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

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
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_34_pp' u hviol hside, exist_st_34_pm' u hviol hside,
    exist_st_34_mp' u hviol hside, exist_st_34_mm' u hviol hside]

private theorem exist_st_52_pp' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 2 1)) u)) <
      vnorm (act (toSL3 (x 2 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 1)) u)) :
    (vnorm (act (toSL3 (x 5 1)) u) < vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 5 1)) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 1)) u) < vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 4 (1 * 1))) (act (toSL3 (x 5 1)) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 (1 * 1))) u) <
        vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 4 (1 * 1))) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-1))) ![-(1 * u 1), 1 * u 0, u 2]) <
        vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 2 (-1)))
          ![-(1 * u 1), 1 * u 0, u 2])) <
        vnorm (act (toSL3 (x 2 1)) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_52_pm' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 2 (-1))) u)) <
      vnorm (act (toSL3 (x 2 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 (-1))) u)) :
    (vnorm (act (toSL3 (x 5 1)) u) < vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 5 1)) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 1)) u) < vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 (1 * (-1)))) (act (toSL3 (x 5 1)) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 (1 * (-1)))) u) <
        vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 4 (1 * (-1)))) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 (-(-1)))) ![-((-1) * u 1), (-1) * u 0, u 2]) <
        vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 1)) (act (toSL3 (x 2 (-(-1))))
          ![-((-1) * u 1), (-1) * u 0, u 2])) <
        vnorm (act (toSL3 (x 2 (-1))) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_52_mp' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 2 1)) u)) <
      vnorm (act (toSL3 (x 2 1)) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 1)) u)) :
    (vnorm (act (toSL3 (x 5 (-1))) u) < vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 2 1)) (act (toSL3 (x 5 (-1))) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 5 (-1))) u) < vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 4 ((-1) * 1))) (act (toSL3 (x 5 (-1))) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 4 ((-1) * 1))) u) <
        vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 4 ((-1) * 1))) u)) <
        vnorm (act (toSL3 (x 2 1)) u)) ∨
    (vnorm (act (toSL3 (x 2 (-1))) ![-(1 * u 1), 1 * u 0, u 2]) <
        vnorm (act (toSL3 (x 2 1)) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 2 (-1)))
          ![-(1 * u 1), 1 * u 0, u 2])) <
        vnorm (act (toSL3 (x 2 1)) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

private theorem exist_st_52_mm' (u : Fin 3 → ℤ)
    (hviol : vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 2 (-1))) u)) <
      vnorm (act (toSL3 (x 2 (-1))) u))
    (hside : vnorm u ≤ vnorm (act (toSL3 (x 2 (-1))) u)) :
    (vnorm (act (toSL3 (x 5 (-1))) u) < vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 2 (-1))) (act (toSL3 (x 5 (-1))) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 5 (-1))) u) < vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 4 ((-1) * (-1)))) (act (toSL3 (x 5 (-1))) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 4 ((-1) * (-1)))) u) <
        vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 4 ((-1) * (-1)))) u)) <
        vnorm (act (toSL3 (x 2 (-1))) u)) ∨
    (vnorm (act (toSL3 (x 2 (-(-1)))) ![-((-1) * u 1), (-1) * u 0, u 2]) <
        vnorm (act (toSL3 (x 2 (-1))) u) ∧
      vnorm (act (toSL3 (x 5 (-1))) (act (toSL3 (x 2 (-(-1))))
          ![-((-1) * u 1), (-1) * u 0, u 2])) <
        vnorm (act (toSL3 (x 2 (-1))) u)) := by
  simp only [act_x2, act_x4, act_x5, vnorm, one_mul, neg_one_mul, neg_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hviol hside ⊢
  lia

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
  rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
  exacts [exist_st_52_pp' u hviol hside, exist_st_52_pm' u hviol hside,
    exist_st_52_mp' u hviol hside, exist_st_52_mm' u hviol hside]

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
      | cons a l => simp

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
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hEpair : eval ([p, q] ++ C) = eval (P' ++ C) := by
    rw [eval_append, eval_append, eval_pair', hid]
  have heval : eval V = eval (A ++ P' ++ C) := by
    calc eval V = eval (A ++ [p, q] ++ C) := by rw [hsplit]
      _ = eval A * eval ([p, q] ++ C) := by
          rw [List.append_assoc, eval_append]
      _ = eval A * eval (P' ++ C) := by rw [hEpair]
      _ = eval (A ++ P' ++ C) := by
          rw [List.append_assoc, eval_append, eval_append, eval_append]
  refine ⟨heval, ?_⟩
  let D : SpliceData V b :=
    ⟨hex, A, P', C, b, by lia, hAlen, hlen, by lia⟩
  have F : SpliceFacts V b D := by
    refine ⟨?_, ?_, ?_⟩
    · -- shallow
      intro j hj
      show sigma (A ++ P' ++ C) b j = sigma V b j
      calc sigma (A ++ P' ++ C) b j
          = sigma (A ++ (P' ++ C)) b j := by rw [List.append_assoc]
        _ = sigma (A ++ ([p, q] ++ C)) b j :=
          sigma_shallow_of_actEq A (P' ++ C) ([p, q] ++ C) b b
            (by rw [hEpair]) j hj
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
    simp only [List.length_append, List.length_cons, List.length_nil]
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
  let D : SpliceData V b :=
    ⟨hex, A, P', C.map f, act (toSL3 wv) b, by lia, hAlen, hlen, by
      rw [List.length_map]; lia⟩
  have F : SpliceFacts V b D := by
    refine ⟨?_, ?_, ?_⟩
    · -- shallow
      intro j hj
      show sigma (A ++ P' ++ C.map f) (act (toSL3 wv) b) j =
        sigma V b j
      have hAct : act (toSL3 (eval (P' ++ C.map f)))
          (act (toSL3 wv) b) = act (toSL3 (eval ([p, q] ++ C))) b := by
        calc act (toSL3 (eval (P' ++ C.map f))) (act (toSL3 wv) b)
            = act (toSL3 (eval (P' ++ C.map f)) * toSL3 wv) b := by
              rw [act_mul]
          _ = act (toSL3 (eval ([p, q] ++ C))) b := by
            rw [← map_mul, hE2]
      calc sigma (A ++ P' ++ C.map f) (act (toSL3 wv) b) j
          = sigma (A ++ (P' ++ C.map f)) (act (toSL3 wv) b) j := by
            rw [List.append_assoc]
        _ = sigma (A ++ ([p, q] ++ C)) b j :=
          sigma_shallow_of_actEq A (P' ++ C.map f) ([p, q] ++ C)
            (act (toSL3 wv) b) b hAct j hj
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
        unfold P13WordDescent.sigma
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

/-! ## Full-package route builders

Each route consumes the split data at the topmost worst violation
together with a replacement-block certificate and produces the
complete descent package: the new word, the new signed-swap tail,
closure, unit letters, the evaluation identity, and the measure
drop. -/

private theorem route_plain (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (P' : List Letter) (hlen : P'.length ≤ 3) (hUP : UnitWord P')
    (hid : eval P' = letterVal p * letterVal q)
    (hcut : ∀ t, 0 < t → t < P'.length →
      vnorm (act (toSL3 (eval (P'.drop t)))
        (vecOf C (act (toSL3 mon) e3))) < lam V (act (toSL3 mon) e3)) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  obtain ⟨heval, hlt⟩ := step_plain V (act (toSL3 mon) e3) hex A C p q
    hsplit hAlen P' hlen hid hcut
  have hUA : UnitWord A := fun l hl => hU l (by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl))))
  have hUC : UnitWord C := fun l hl => hU l (by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr hl))
  exact ⟨A ++ P' ++ C, mon, hmon,
    unitWord_append (unitWord_append hUA hUP) hUC,
    by rw [heval], hlt⟩

private theorem route_emit (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (P' : List Letter) (hlen : P'.length ≤ 3) (hUP : UnitWord P')
    (wv : P13) (hwv : wv ∈ Subgroup.closure ({w13, w23} : Set P13))
    (f : Letter → Letter)
    (hf : ∀ l, wv * letterVal l * wv⁻¹ = letterVal (f l))
    (hfsign : ∀ l : Letter, (f l).2 = l.2 ∨ (f l).2 = -l.2)
    (hnorm : ∀ z, vnorm (act (toSL3 wv) z) = vnorm z)
    (hid : eval P' * wv = letterVal p * letterVal q)
    (hcut : ∀ t, 0 < t → t < P'.length →
      vnorm (act (toSL3 (eval (P'.drop t)))
        (act (toSL3 wv) (vecOf C (act (toSL3 mon) e3)))) <
        lam V (act (toSL3 mon) e3)) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  obtain ⟨heval, hlt⟩ := step_emit V (act (toSL3 mon) e3) hex A C p q
    hsplit hAlen P' hlen wv f hf hnorm hid hcut
  have hUA : UnitWord A := fun l hl => hU l (by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl))))
  have hUC : UnitWord C := fun l hl => hU l (by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr hl))
  refine ⟨A ++ P' ++ C.map f, wv * mon,
    Subgroup.mul_mem _ hwv hmon,
    unitWord_append (unitWord_append hUA hUP) (unitWord_map hfsign hUC),
    ?_, ?_⟩
  · rw [heval, mul_assoc]
  · have hbase : act (toSL3 (wv * mon)) e3 =
        act (toSL3 wv) (act (toSL3 mon) e3) := by
      rw [map_mul, act_mul]
    rw [hbase]
    exact hlt

private theorem route_nil (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (hid0 : letterVal p * letterVal q = 1) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  refine route_plain V mon hmon hU hex A C p q hsplit hAlen []
    (by norm_num) unitWord_nil (by rw [eval_nil, hid0]) ?_
  intro t _ htl
  simp only [List.length_nil] at htl
  lia

private theorem route_pair (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (l₁ l₂ : Letter)
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) (h₂ : l₂.2 = 1 ∨ l₂.2 = -1)
    (hid2 : letterVal l₁ * letterVal l₂ = letterVal p * letterVal q)
    (h1 : vnorm (act (toSL3 (letterVal l₂))
      (vecOf C (act (toSL3 mon) e3))) < lam V (act (toSL3 mon) e3)) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  refine route_plain V mon hmon hU hex A C p q hsplit hAlen [l₁, l₂]
    (by norm_num) (unitWord_pair h₁ h₂)
    (by rw [eval_pair']; exact hid2) ?_
  intro t ht0 htl
  simp only [List.length_cons, List.length_nil] at htl
  have ht1 : t = 1 := by lia
  subst ht1
  show vnorm (act (toSL3 (eval [l₂]))
    (vecOf C (act (toSL3 mon) e3))) < lam V (act (toSL3 mon) e3)
  rw [eval_single]
  exact h1

private theorem route_triple (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (l₁ l₂ l₃ : Letter)
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) (h₂ : l₂.2 = 1 ∨ l₂.2 = -1)
    (h₃ : l₃.2 = 1 ∨ l₃.2 = -1)
    (hid3 : letterVal l₁ * letterVal l₂ * letterVal l₃ =
      letterVal p * letterVal q)
    (h1 : vnorm (act (toSL3 (letterVal l₃))
      (vecOf C (act (toSL3 mon) e3))) < lam V (act (toSL3 mon) e3))
    (h2 : vnorm (act (toSL3 (letterVal l₂)) (act (toSL3 (letterVal l₃))
      (vecOf C (act (toSL3 mon) e3)))) < lam V (act (toSL3 mon) e3)) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  refine route_plain V mon hmon hU hex A C p q hsplit hAlen
    [l₁, l₂, l₃] (by norm_num) (unitWord_triple h₁ h₂ h₃)
    (by rw [eval_triple]; exact hid3) ?_
  intro t ht0 htl
  simp only [List.length_cons, List.length_nil] at htl
  have ht : t = 1 ∨ t = 2 := by lia
  rcases ht with rfl | rfl
  · show vnorm (act (toSL3 (eval [l₂, l₃]))
      (vecOf C (act (toSL3 mon) e3))) < lam V (act (toSL3 mon) e3)
    rw [eval_pair', map_mul, act_mul]
    exact h2
  · show vnorm (act (toSL3 (eval [l₃]))
      (vecOf C (act (toSL3 mon) e3))) < lam V (act (toSL3 mon) e3)
    rw [eval_single]
    exact h1

private theorem route_single_emit (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (l₁ : Letter) (h₁ : l₁.2 = 1 ∨ l₁.2 = -1)
    (wv : P13) (hwv : wv ∈ Subgroup.closure ({w13, w23} : Set P13))
    (f : Letter → Letter)
    (hf : ∀ l, wv * letterVal l * wv⁻¹ = letterVal (f l))
    (hfsign : ∀ l : Letter, (f l).2 = l.2 ∨ (f l).2 = -l.2)
    (hnorm : ∀ z, vnorm (act (toSL3 wv) z) = vnorm z)
    (hid1 : letterVal l₁ * wv = letterVal p * letterVal q) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  refine route_emit V mon hmon hU hex A C p q hsplit hAlen [l₁]
    (by norm_num) (unitWord_single h₁) wv hwv f hf hfsign hnorm
    (by rw [eval_single]; exact hid1) ?_
  intro t ht0 htl
  simp only [List.length_cons, List.length_nil] at htl
  lia

private theorem route_triple_emit (V : List Letter) (mon : P13)
    (hmon : mon ∈ Subgroup.closure ({w13, w23} : Set P13))
    (hU : UnitWord V)
    (hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) = lam V (act (toSL3 mon) e3))
    (A C : List Letter) (p q : Letter)
    (hsplit : V = A ++ [p, q] ++ C)
    (hAlen : A.length = topViol V (act (toSL3 mon) e3) hex)
    (l₁ l₂ l₃ : Letter)
    (h₁ : l₁.2 = 1 ∨ l₁.2 = -1) (h₂ : l₂.2 = 1 ∨ l₂.2 = -1)
    (h₃ : l₃.2 = 1 ∨ l₃.2 = -1)
    (wv : P13) (hwv : wv ∈ Subgroup.closure ({w13, w23} : Set P13))
    (f : Letter → Letter)
    (hf : ∀ l, wv * letterVal l * wv⁻¹ = letterVal (f l))
    (hfsign : ∀ l : Letter, (f l).2 = l.2 ∨ (f l).2 = -l.2)
    (hnorm : ∀ z, vnorm (act (toSL3 wv) z) = vnorm z)
    (hid3 : letterVal l₁ * letterVal l₂ * letterVal l₃ * wv =
      letterVal p * letterVal q)
    (h1 : vnorm (act (toSL3 (letterVal l₃))
      (act (toSL3 wv) (vecOf C (act (toSL3 mon) e3)))) <
      lam V (act (toSL3 mon) e3))
    (h2 : vnorm (act (toSL3 (letterVal l₂)) (act (toSL3 (letterVal l₃))
      (act (toSL3 wv) (vecOf C (act (toSL3 mon) e3))))) <
      lam V (act (toSL3 mon) e3)) :
    ∃ (V' : List Letter) (mon' : P13),
      mon' ∈ Subgroup.closure ({w13, w23} : Set P13) ∧
      UnitWord V' ∧
      eval V * mon = eval V' * mon' ∧
      Prod.Lex (· < ·) (· < ·)
        (meas V' (act (toSL3 mon') e3))
        (meas V (act (toSL3 mon) e3)) := by
  refine route_emit V mon hmon hU hex A C p q hsplit hAlen
    [l₁, l₂, l₃] (by norm_num) (unitWord_triple h₁ h₂ h₃)
    wv hwv f hf hfsign hnorm (by rw [eval_triple]; exact hid3) ?_
  intro t ht0 htl
  simp only [List.length_cons, List.length_nil] at htl
  have ht : t = 1 ∨ t = 2 := by lia
  rcases ht with rfl | rfl
  · show vnorm (act (toSL3 (eval [l₂, l₃]))
      (act (toSL3 wv) (vecOf C (act (toSL3 mon) e3)))) <
      lam V (act (toSL3 mon) e3)
    rw [eval_pair', map_mul, act_mul]
    exact h2
  · show vnorm (act (toSL3 (eval [l₃]))
      (act (toSL3 wv) (vecOf C (act (toSL3 mon) e3)))) <
      lam V (act (toSL3 mon) e3)
    rw [eval_single]
    exact h1

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
  obtain ⟨j₀, hj₀⟩ := hviol
  have hex : ∃ j, Viol V (act (toSL3 mon) e3) j ∧
      sigma V (act (toSL3 mon) e3) (j + 1) =
        lam V (act (toSL3 mon) e3) := exists_top hj₀
  have hb1 : vnorm (act (toSL3 mon) e3) = 1 :=
    vnorm_corner (isCorner_of_closure hmon)
  obtain ⟨hvTop, htop⟩ := topViol_spec hex
  set v := topViol V (act (toSL3 mon) e3) hex with hv_def
  have hvlt : v + 1 < V.length := viol_succ_lt hb1 hvTop
  have hvlt0 : v < V.length := by lia
  have hsplit := word_split V v hvlt
  rcases hpq : V[v] with ⟨i, c⟩
  rcases hq : V[v + 1] with ⟨ip, cp⟩
  rw [hpq, hq] at hsplit
  set A := V.take v with hA_def
  set C := V.drop (v + 2)
  have hAlen : A.length = v := by
    rw [hA_def, List.length_take]
    exact Nat.min_eq_left (Nat.le_of_lt hvlt0)
  have hc : c = 1 ∨ c = -1 := by
    have hm : ((i, c) : Letter) ∈ V := by
      rw [hsplit]; simp
    exact hU _ hm
  have hcp : cp = 1 ∨ cp = -1 := by
    have hm : ((ip, cp) : Letter) ∈ V := by
      rw [hsplit]; simp
    exact hU _ hm
  obtain ⟨hσ0, hσ1, hσ2⟩ := sigma_pair_coords A C (i, c) (ip, cp)
    (act (toSL3 mon) e3)
  rw [← hsplit, hAlen] at hσ0 hσ1 hσ2
  have hviolC : vnorm (act (toSL3 (x i c)) (act (toSL3 (x ip cp))
      (vecOf C (act (toSL3 mon) e3)))) <
      vnorm (act (toSL3 (x ip cp)) (vecOf C (act (toSL3 mon) e3))) := by
    obtain ⟨-, h⟩ := hvTop
    rw [hσ0, hσ1] at h
    exact h
  have hlamC : vnorm (act (toSL3 (x ip cp))
      (vecOf C (act (toSL3 mon) e3))) =
      lam V (act (toSL3 mon) e3) := by
    have h := htop
    rw [hσ1] at h
    exact h
  have hsideC : vnorm (vecOf C (act (toSL3 mon) e3)) ≤
      vnorm (act (toSL3 (x ip cp)) (vecOf C (act (toSL3 mon) e3))) := by
    have h := side_le_of_top hex
    rw [← hv_def] at h
    rw [hσ1, hσ2] at h
    exact h
  fin_cases i <;> fin_cases ip
  · -- (0, 0): same family
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (same_aligned_0 1 (Or.inl rfl) _ hviolC hsideC).elim
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ 1)
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ (-1))
    · exact (same_aligned_0 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (0, 1): same write
    rcases exist_sw_01 c cp hc hcp _ hviolC hsideC with
      h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, cp) : Letter) ((0, c) : Letter) hcp hc
        ((x_commute_12_13 c cp).eq.symm) (lt_of_lt_of_eq h1 hlamC)
    · have hs := sand3_conj (-(c * cp)) c
      rw [neg_neg] at hs
      have he : -(-(c * cp) * c) = cp := by
        rcases hc with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, -(c * cp)) : Letter) ((0, c) : Letter)
        ((3, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hc (unit_mul hc hcp)
        (hs.trans ((x_commute_12_13 c cp).eq.symm))
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · have hs := sand5_conj (-(c * cp)) cp
      rw [neg_neg] at hs
      have he : -(-(c * cp) * cp) = c := by
        rcases hcp with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, -(c * cp)) : Letter) ((1, cp) : Letter)
        ((5, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hcp (unit_mul hc hcp)
        hs
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (0, 2): braid pair
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (braid_aligned_02 1 (Or.inl rfl) _ hviolC hsideC).elim
    · have hid1 : x 2 1 * w = x 0 1 * x 2 (-1) := by
        calc x 2 1 * w
            = x 2 1 * (x 2 (-1) * x 0 1 * x 2 (-1)) := by
              rw [← nu_w_neg]
          _ = x 2 1 * x 2 (-1) * (x 0 1 * x 2 (-1)) := by
              group
          _ = x 0 1 * x 2 (-1) := by
              rw [x_add, show (1 : ℤ) + -1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, 1) : Letter) (Or.inl rfl)
        w w_mem_closure wConj w_conj_letter wConj_sign
        vnorm_act_w hid1
    · have hid1 : x 2 (-1) * w⁻¹ = x 0 (-1) * x 2 1 := by
        calc x 2 (-1) * w⁻¹
            = x 2 (-1) * (x 2 1 * x 0 (-1) * x 2 1) := by
              rw [← nu_w_pos]
          _ = x 2 (-1) * x 2 1 * (x 0 (-1) * x 2 1) := by
              group
          _ = x 0 (-1) * x 2 1 := by
              rw [x_add, show (-1 : ℤ) + 1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, -1) : Letter) (Or.inr rfl)
        w⁻¹ (Subgroup.inv_mem _ w_mem_closure) wConjInv winv_hf
        wConjInv_sign vnorm_act_winv hid1
    · exact (braid_aligned_02 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (0, 3): Steinberg pair, forward
    rcases exist_st_03 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, c * cp) : Letter) ((3, cp) : Letter)
        ((0, c) : Letter)
        (unit_mul hc hcp) hcp hc ((st_03 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, cp) : Letter) ((1, c * cp) : Letter)
        ((0, c) : Letter)
        hcp (unit_mul hc hcp) hc ((st_03_mid c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, cp) : Letter) ((0, c) : Letter)
        ((1, c * cp) : Letter)
        hcp hc (unit_mul hc hcp) ((st_03_last c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hcp with rfl | rfl
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0, 1 * vecOf C (act (toSL3 mon) e3) 2,
          -(1 * vecOf C (act (toSL3 mon) e3) 1)] :
          Fin 3 → ℤ) =
          act (toSL3 w23) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 5 1 * x 0 c * x 3 (-1) *
          (x 3 1 * x 5 (-1) * x 3 1) =
          x 0 c * x 3 1 := em_03 c 1
        rw [pi_w23_pos] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((5, 1) : Letter) ((0, c) : Letter)
          ((3, -1) : Letter)
          (Or.inl rfl) hc (Or.inr rfl)
          w23 w23_mem_closure w23Conj w23_conj_letter w23Conj_sign
          vnorm_act_w23 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0, -1 * vecOf C (act (toSL3 mon) e3) 2,
          -(-1 * vecOf C (act (toSL3 mon) e3) 1)] :
          Fin 3 → ℤ) =
          act (toSL3 w23⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23inv_vec]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 5 (-1) * x 0 c * x 3 1 *
          (x 3 (-1) * x 5 1 * x 3 (-1)) =
          x 0 c * x 3 (-1) := em_03 c (-1)
        rw [pi_w23_neg] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((5, -1) : Letter) ((0, c) : Letter)
          ((3, 1) : Letter)
          (Or.inr rfl) hc (Or.inl rfl)
          w23⁻¹ (Subgroup.inv_mem _ w23_mem_closure) w23ConjInv
          w23inv_hf w23ConjInv_sign vnorm_act_w23inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (0, 4): Steinberg pair, reversed
    rcases exist_st_04 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, -(cp * c)) : Letter) ((4, cp) : Letter)
        ((0, c) : Letter)
        (unit_neg (unit_mul hcp hc)) hcp hc ((stB_04 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hc with rfl | rfl
      · have hB : (![vecOf C (act (toSL3 mon) e3) 1,
            -(vecOf C (act (toSL3 mon) e3) 0),
            vecOf C (act (toSL3 mon) e3) 2] : Fin 3 → ℤ) =
            act (toSL3 w) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w]
        simp only [one_mul] at h1 h2
        rw [hB] at h1 h2
        have hem : x 2 1 * x 5 (-cp) * x 0 (-1) * w = x 0 1 * x 4 cp := by
          have h := emR_04 1 cp (Or.inl rfl)
          rw [show (-(1 * cp) : ℤ) = -cp from by ring] at h
          rw [pi_w_pos] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((2, 1) : Letter) ((5, -cp) : Letter)
          ((0, -1) : Letter)
          (Or.inl rfl) (unit_neg hcp) (Or.inr rfl)
          w w_mem_closure wConj w_conj_letter wConj_sign
          vnorm_act_w hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![-(vecOf C (act (toSL3 mon) e3) 1),
            vecOf C (act (toSL3 mon) e3) 0,
            vecOf C (act (toSL3 mon) e3) 2] : Fin 3 → ℤ) =
            act (toSL3 w⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_winv_vec]
        simp only [neg_one_mul, neg_neg] at h1 h2
        rw [hB] at h1 h2
        have hem : x 2 (-1) * x 5 cp * x 0 1 * w⁻¹ = x 0 (-1) * x 4 cp := by
          have h := emR_04 (-1) cp (Or.inr rfl)
          rw [show (-(-1 * cp) : ℤ) = cp from by ring,
            show (-(-1) : ℤ) = 1 from by norm_num] at h
          rw [pi_w_neg] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((2, -1) : Letter) ((5, cp) : Letter)
          ((0, 1) : Letter)
          (Or.inr rfl) hcp (Or.inl rfl)
          w⁻¹ (Subgroup.inv_mem _ w_mem_closure) wConjInv winv_hf wConjInv_sign
          vnorm_act_winv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (0, 5): same read — swap
    have h1 := exist_sr_05 c cp hc hcp _ hviolC hsideC
    exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
      ((5, cp) : Letter) ((0, c) : Letter) hcp hc
      ((x_commute_12_32 c cp).eq.symm)
      (lt_of_lt_of_eq h1 hlamC)
  · -- (1, 0): same write
    rcases exist_sw_10 c cp hc hcp _ hviolC hsideC with
      h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, cp) : Letter) ((1, c) : Letter) hcp hc
        ((x_commute_12_13 cp c).eq) (lt_of_lt_of_eq h1 hlamC)
    · have hs := sand5_conj (-(c * cp)) c
      rw [neg_neg] at hs
      have he : -(-(c * cp) * c) = cp := by
        rcases hc with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, -(c * cp)) : Letter) ((1, c) : Letter)
        ((5, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hc (unit_mul hc hcp)
        (hs.trans ((x_commute_12_13 cp c).eq))
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · have hs := sand3_conj (-(c * cp)) cp
      rw [neg_neg] at hs
      have he : -(-(c * cp) * cp) = c := by
        rcases hcp with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, -(c * cp)) : Letter) ((0, cp) : Letter)
        ((3, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hcp (unit_mul hc hcp)
        hs
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (1, 1): same family
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (same_aligned_1 1 (Or.inl rfl) _ hviolC hsideC).elim
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ 1)
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ (-1))
    · exact (same_aligned_1 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (1, 2): Steinberg pair, reversed
    rcases exist_st_12 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, -(cp * c)) : Letter) ((2, cp) : Letter)
        ((1, c) : Letter)
        (unit_neg (unit_mul hcp hc)) hcp hc ((stB_12 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hc with rfl | rfl
      · have hB : (![vecOf C (act (toSL3 mon) e3) 2,
            vecOf C (act (toSL3 mon) e3) 1,
            -(vecOf C (act (toSL3 mon) e3) 0)] : Fin 3 → ℤ) =
            act (toSL3 w13) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13]
        simp only [one_mul] at h1 h2
        rw [hB] at h1 h2
        have hem : x 4 1 * x 3 (-cp) * x 1 (-1) * w13 = x 1 1 * x 2 cp := by
          have h := emR_12 1 cp (Or.inl rfl)
          rw [show (-(1 * cp) : ℤ) = -cp from by ring] at h
          rw [pi_w13_pos] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((4, 1) : Letter) ((3, -cp) : Letter)
          ((1, -1) : Letter)
          (Or.inl rfl) (unit_neg hcp) (Or.inr rfl)
          w13 w13_mem_closure w13Conj w13_conj_letter w13Conj_sign
          vnorm_act_w13 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![-(vecOf C (act (toSL3 mon) e3) 2),
            vecOf C (act (toSL3 mon) e3) 1,
            vecOf C (act (toSL3 mon) e3) 0] : Fin 3 → ℤ) =
            act (toSL3 w13⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13inv_vec]
        simp only [neg_one_mul, neg_neg] at h1 h2
        rw [hB] at h1 h2
        have hem : x 4 (-1) * x 3 cp * x 1 1 * w13⁻¹ = x 1 (-1) * x 2 cp := by
          have h := emR_12 (-1) cp (Or.inr rfl)
          rw [show (-(-1 * cp) : ℤ) = cp from by ring,
            show (-(-1) : ℤ) = 1 from by norm_num] at h
          rw [pi_w13_neg] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((4, -1) : Letter) ((3, cp) : Letter)
          ((1, 1) : Letter)
          (Or.inr rfl) hcp (Or.inl rfl)
          w13⁻¹ (Subgroup.inv_mem _ w13_mem_closure) w13ConjInv w13inv_hf w13ConjInv_sign
          vnorm_act_w13inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (1, 3): same read — swap
    have h1 := exist_sr_13 c cp hc hcp _ hviolC hsideC
    exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
      ((3, cp) : Letter) ((1, c) : Letter) hcp hc
      ((x_commute_13_23 c cp).eq.symm)
      (lt_of_lt_of_eq h1 hlamC)
  · -- (1, 4): braid pair
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (braid_aligned_14 1 (Or.inl rfl) _ hviolC hsideC).elim
    · have hid1 : x 4 1 * w13 = x 1 1 * x 4 (-1) := by
        calc x 4 1 * w13
            = x 4 1 * (x 4 (-1) * x 1 1 * x 4 (-1)) := by
              rw [← nu_w13_neg]
          _ = x 4 1 * x 4 (-1) * (x 1 1 * x 4 (-1)) := by
              group
          _ = x 1 1 * x 4 (-1) := by
              rw [x_add, show (1 : ℤ) + -1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, 1) : Letter) (Or.inl rfl)
        w13 w13_mem_closure w13Conj w13_conj_letter w13Conj_sign
        vnorm_act_w13 hid1
    · have hid1 : x 4 (-1) * w13⁻¹ = x 1 (-1) * x 4 1 := by
        calc x 4 (-1) * w13⁻¹
            = x 4 (-1) * (x 4 1 * x 1 (-1) * x 4 1) := by
              rw [← nu_w13_pos]
          _ = x 4 (-1) * x 4 1 * (x 1 (-1) * x 4 1) := by
              group
          _ = x 1 (-1) * x 4 1 := by
              rw [x_add, show (-1 : ℤ) + 1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, -1) : Letter) (Or.inr rfl)
        w13⁻¹ (Subgroup.inv_mem _ w13_mem_closure) w13ConjInv
        w13inv_hf w13ConjInv_sign vnorm_act_w13inv hid1
    · exact (braid_aligned_14 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (1, 5): Steinberg pair, forward
    rcases exist_st_15' c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, c * cp) : Letter) ((5, cp) : Letter)
        ((1, c) : Letter)
        (unit_mul hc hcp) hcp hc ((st_15 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, cp) : Letter) ((0, c * cp) : Letter)
        ((1, c) : Letter)
        hcp (unit_mul hc hcp) hc ((st_15_mid c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, cp) : Letter) ((1, c) : Letter)
        ((0, c * cp) : Letter)
        hcp hc (unit_mul hc hcp) ((st_15_last c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hcp with rfl | rfl
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0, -(1 * vecOf C (act (toSL3 mon) e3) 2),
          1 * vecOf C (act (toSL3 mon) e3) 1] :
          Fin 3 → ℤ) =
          act (toSL3 w23⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23inv_vec]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 3 1 * x 1 c * x 5 (-1) *
          (x 5 1 * x 3 (-1) * x 5 1) =
          x 1 c * x 5 1 := em_15 c 1
        rw [nu_w23_pos] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((3, 1) : Letter) ((1, c) : Letter)
          ((5, -1) : Letter)
          (Or.inl rfl) hc (Or.inr rfl)
          w23⁻¹ (Subgroup.inv_mem _ w23_mem_closure) w23ConjInv
          w23inv_hf w23ConjInv_sign vnorm_act_w23inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0, -(-1 * vecOf C (act (toSL3 mon) e3) 2),
          -1 * vecOf C (act (toSL3 mon) e3) 1] :
          Fin 3 → ℤ) =
          act (toSL3 w23) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 3 (-1) * x 1 c * x 5 1 *
          (x 5 (-1) * x 3 1 * x 5 (-1)) =
          x 1 c * x 5 (-1) := em_15 c (-1)
        rw [nu_w23_neg] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((3, -1) : Letter) ((1, c) : Letter)
          ((5, 1) : Letter)
          (Or.inr rfl) hc (Or.inl rfl)
          w23 w23_mem_closure w23Conj w23_conj_letter w23Conj_sign
          vnorm_act_w23 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (2, 0): braid pair, reversed
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (braid_aligned_20 1 (Or.inl rfl) _ hviolC hsideC).elim
    · have hid1 : x 0 1 * w⁻¹ = x 2 1 * x 0 (-1) := by
        calc x 0 1 * w⁻¹
            = x 0 1 * (x 0 (-1) * x 2 1 * x 0 (-1)) := by
              rw [← pi_w_neg]
          _ = x 0 1 * x 0 (-1) * (x 2 1 * x 0 (-1)) := by
              group
          _ = x 2 1 * x 0 (-1) := by
              rw [x_add, show (1 : ℤ) + -1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, 1) : Letter) (Or.inl rfl)
        w⁻¹ (Subgroup.inv_mem _ w_mem_closure) wConjInv winv_hf
        wConjInv_sign vnorm_act_winv hid1
    · have hid1 : x 0 (-1) * w = x 2 (-1) * x 0 1 := by
        calc x 0 (-1) * w
            = x 0 (-1) * (x 0 1 * x 2 (-1) * x 0 1) := by
              rw [← pi_w_pos]
          _ = x 0 (-1) * x 0 1 * (x 2 (-1) * x 0 1) := by
              group
          _ = x 2 (-1) * x 0 1 := by
              rw [x_add, show (-1 : ℤ) + 1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, -1) : Letter) (Or.inr rfl)
        w w_mem_closure wConj w_conj_letter wConj_sign
        vnorm_act_w hid1
    · exact (braid_aligned_20 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (2, 1): Steinberg pair, forward
    rcases exist_st_21 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, c * cp) : Letter) ((1, cp) : Letter)
        ((2, c) : Letter)
        (unit_mul hc hcp) hcp hc ((st_21 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, cp) : Letter) ((3, c * cp) : Letter)
        ((2, c) : Letter)
        hcp (unit_mul hc hcp) hc ((st_21_mid c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, cp) : Letter) ((2, c) : Letter)
        ((3, c * cp) : Letter)
        hcp hc (unit_mul hc hcp) ((st_21_last c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hcp with rfl | rfl
      · have hB : (![1 * vecOf C (act (toSL3 mon) e3) 2, vecOf C (act (toSL3 mon) e3) 1,
          -(1 * vecOf C (act (toSL3 mon) e3) 0)] :
          Fin 3 → ℤ) =
          act (toSL3 w13) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 4 1 * x 2 c * x 1 (-1) *
          (x 1 1 * x 4 (-1) * x 1 1) =
          x 2 c * x 1 1 := em_21 c 1
        rw [pi_w13_pos] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((4, 1) : Letter) ((2, c) : Letter)
          ((1, -1) : Letter)
          (Or.inl rfl) hc (Or.inr rfl)
          w13 w13_mem_closure w13Conj w13_conj_letter w13Conj_sign
          vnorm_act_w13 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![-1 * vecOf C (act (toSL3 mon) e3) 2, vecOf C (act (toSL3 mon) e3) 1,
          -(-1 * vecOf C (act (toSL3 mon) e3) 0)] :
          Fin 3 → ℤ) =
          act (toSL3 w13⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13inv_vec]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 4 (-1) * x 2 c * x 1 1 *
          (x 1 (-1) * x 4 1 * x 1 (-1)) =
          x 2 c * x 1 (-1) := em_21 c (-1)
        rw [pi_w13_neg] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((4, -1) : Letter) ((2, c) : Letter)
          ((1, 1) : Letter)
          (Or.inr rfl) hc (Or.inl rfl)
          w13⁻¹ (Subgroup.inv_mem _ w13_mem_closure) w13ConjInv
          w13inv_hf w13ConjInv_sign vnorm_act_w13inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (2, 2): same family
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (same_aligned_2 1 (Or.inl rfl) _ hviolC hsideC).elim
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ 1)
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ (-1))
    · exact (same_aligned_2 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (2, 3): same write
    rcases exist_sw_23 c cp hc hcp _ hviolC hsideC with
      h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, cp) : Letter) ((2, c) : Letter) hcp hc
        ((x_commute_21_23 c cp).eq.symm) (lt_of_lt_of_eq h1 hlamC)
    · have hs := sand1_conj (-(c * cp)) c
      rw [neg_neg] at hs
      have he : -(-(c * cp) * c) = cp := by
        rcases hc with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, -(c * cp)) : Letter) ((2, c) : Letter)
        ((1, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hc (unit_mul hc hcp)
        (hs.trans ((x_commute_21_23 c cp).eq.symm))
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · have hs := sand4_conj (-(c * cp)) cp
      rw [neg_neg] at hs
      have he : -(-(c * cp) * cp) = c := by
        rcases hcp with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, -(c * cp)) : Letter) ((3, cp) : Letter)
        ((4, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hcp (unit_mul hc hcp)
        hs
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (2, 4): same read — swap
    have h1 := exist_sr_24 c cp hc hcp _ hviolC hsideC
    exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
      ((4, cp) : Letter) ((2, c) : Letter) hcp hc
      ((x_commute_21_31 c cp).eq.symm)
      (lt_of_lt_of_eq h1 hlamC)
  · -- (2, 5): Steinberg pair, reversed
    rcases exist_st_25 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, -(cp * c)) : Letter) ((5, cp) : Letter)
        ((2, c) : Letter)
        (unit_neg (unit_mul hcp hc)) hcp hc ((stB_25 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hc with rfl | rfl
      · have hB : (![-(vecOf C (act (toSL3 mon) e3) 1),
            vecOf C (act (toSL3 mon) e3) 0,
            vecOf C (act (toSL3 mon) e3) 2] : Fin 3 → ℤ) =
            act (toSL3 w⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_winv_vec]
        simp only [one_mul] at h1 h2
        rw [hB] at h1 h2
        have hem : x 0 1 * x 4 (-cp) * x 2 (-1) * w⁻¹ = x 2 1 * x 5 cp := by
          have h := emR_25 1 cp (Or.inl rfl)
          rw [show (-(1 * cp) : ℤ) = -cp from by ring] at h
          rw [nu_w_pos] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((0, 1) : Letter) ((4, -cp) : Letter)
          ((2, -1) : Letter)
          (Or.inl rfl) (unit_neg hcp) (Or.inr rfl)
          w⁻¹ (Subgroup.inv_mem _ w_mem_closure) wConjInv winv_hf wConjInv_sign
          vnorm_act_winv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![vecOf C (act (toSL3 mon) e3) 1,
            -(vecOf C (act (toSL3 mon) e3) 0),
            vecOf C (act (toSL3 mon) e3) 2] : Fin 3 → ℤ) =
            act (toSL3 w) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w]
        simp only [neg_one_mul, neg_neg] at h1 h2
        rw [hB] at h1 h2
        have hem : x 0 (-1) * x 4 cp * x 2 1 * w = x 2 (-1) * x 5 cp := by
          have h := emR_25 (-1) cp (Or.inr rfl)
          rw [show (-(-1 * cp) : ℤ) = cp from by ring,
            show (-(-1) : ℤ) = 1 from by norm_num] at h
          rw [nu_w_neg] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((0, -1) : Letter) ((4, cp) : Letter)
          ((2, 1) : Letter)
          (Or.inr rfl) hcp (Or.inl rfl)
          w w_mem_closure wConj w_conj_letter wConj_sign
          vnorm_act_w hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (3, 0): Steinberg pair, reversed
    rcases exist_st_30 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, -(cp * c)) : Letter) ((0, cp) : Letter)
        ((3, c) : Letter)
        (unit_neg (unit_mul hcp hc)) hcp hc ((stB_30 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hc with rfl | rfl
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0,
            vecOf C (act (toSL3 mon) e3) 2,
            -(vecOf C (act (toSL3 mon) e3) 1)] : Fin 3 → ℤ) =
            act (toSL3 w23) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23]
        simp only [one_mul] at h1 h2
        rw [hB] at h1 h2
        have hem : x 5 1 * x 1 (-cp) * x 3 (-1) * w23 = x 3 1 * x 0 cp := by
          have h := emR_30 1 cp (Or.inl rfl)
          rw [show (-(1 * cp) : ℤ) = -cp from by ring] at h
          rw [pi_w23_pos] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((5, 1) : Letter) ((1, -cp) : Letter)
          ((3, -1) : Letter)
          (Or.inl rfl) (unit_neg hcp) (Or.inr rfl)
          w23 w23_mem_closure w23Conj w23_conj_letter w23Conj_sign
          vnorm_act_w23 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0,
            -(vecOf C (act (toSL3 mon) e3) 2),
            vecOf C (act (toSL3 mon) e3) 1] : Fin 3 → ℤ) =
            act (toSL3 w23⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23inv_vec]
        simp only [neg_one_mul, neg_neg] at h1 h2
        rw [hB] at h1 h2
        have hem : x 5 (-1) * x 1 cp * x 3 1 * w23⁻¹ = x 3 (-1) * x 0 cp := by
          have h := emR_30 (-1) cp (Or.inr rfl)
          rw [show (-(-1 * cp) : ℤ) = cp from by ring,
            show (-(-1) : ℤ) = 1 from by norm_num] at h
          rw [pi_w23_neg] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((5, -1) : Letter) ((1, cp) : Letter)
          ((3, 1) : Letter)
          (Or.inr rfl) hcp (Or.inl rfl)
          w23⁻¹ (Subgroup.inv_mem _ w23_mem_closure) w23ConjInv w23inv_hf w23ConjInv_sign
          vnorm_act_w23inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (3, 1): same read — swap
    have h1 := exist_sr_31 c cp hc hcp _ hviolC hsideC
    exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
      ((1, cp) : Letter) ((3, c) : Letter) hcp hc
      ((x_commute_13_23 cp c).eq)
      (lt_of_lt_of_eq h1 hlamC)
  · -- (3, 2): same write
    rcases exist_sw_32 c cp hc hcp _ hviolC hsideC with
      h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, cp) : Letter) ((3, c) : Letter) hcp hc
        ((x_commute_21_23 cp c).eq) (lt_of_lt_of_eq h1 hlamC)
    · have hs := sand4_conj (-(c * cp)) c
      rw [neg_neg] at hs
      have he : -(-(c * cp) * c) = cp := by
        rcases hc with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, -(c * cp)) : Letter) ((3, c) : Letter)
        ((4, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hc (unit_mul hc hcp)
        (hs.trans ((x_commute_21_23 cp c).eq))
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · have hs := sand1_conj (-(c * cp)) cp
      rw [neg_neg] at hs
      have he : -(-(c * cp) * cp) = c := by
        rcases hcp with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, -(c * cp)) : Letter) ((2, cp) : Letter)
        ((1, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hcp (unit_mul hc hcp)
        hs
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (3, 3): same family
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (same_aligned_3 1 (Or.inl rfl) _ hviolC hsideC).elim
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ 1)
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ (-1))
    · exact (same_aligned_3 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (3, 4): Steinberg pair, forward
    rcases exist_st_34' c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, c * cp) : Letter) ((4, cp) : Letter)
        ((3, c) : Letter)
        (unit_mul hc hcp) hcp hc ((st_34 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, cp) : Letter) ((2, c * cp) : Letter)
        ((3, c) : Letter)
        hcp (unit_mul hc hcp) hc ((st_34_mid c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, cp) : Letter) ((3, c) : Letter)
        ((2, c * cp) : Letter)
        hcp hc (unit_mul hc hcp) ((st_34_last c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hcp with rfl | rfl
      · have hB : (![-(1 * vecOf C (act (toSL3 mon) e3) 2), vecOf C (act (toSL3 mon) e3) 1,
          1 * vecOf C (act (toSL3 mon) e3) 0] :
          Fin 3 → ℤ) =
          act (toSL3 w13⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13inv_vec]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 1 1 * x 3 c * x 4 (-1) *
          (x 4 1 * x 1 (-1) * x 4 1) =
          x 3 c * x 4 1 := em_34 c 1
        rw [nu_w13_pos] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((1, 1) : Letter) ((3, c) : Letter)
          ((4, -1) : Letter)
          (Or.inl rfl) hc (Or.inr rfl)
          w13⁻¹ (Subgroup.inv_mem _ w13_mem_closure) w13ConjInv
          w13inv_hf w13ConjInv_sign vnorm_act_w13inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![-(-1 * vecOf C (act (toSL3 mon) e3) 2), vecOf C (act (toSL3 mon) e3) 1,
          -1 * vecOf C (act (toSL3 mon) e3) 0] :
          Fin 3 → ℤ) =
          act (toSL3 w13) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 1 (-1) * x 3 c * x 4 1 *
          (x 4 (-1) * x 1 1 * x 4 (-1)) =
          x 3 c * x 4 (-1) := em_34 c (-1)
        rw [nu_w13_neg] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((1, -1) : Letter) ((3, c) : Letter)
          ((4, 1) : Letter)
          (Or.inr rfl) hc (Or.inl rfl)
          w13 w13_mem_closure w13Conj w13_conj_letter w13Conj_sign
          vnorm_act_w13 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (3, 5): braid pair
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (braid_aligned_35 1 (Or.inl rfl) _ hviolC hsideC).elim
    · have hid1 : x 5 1 * w23 = x 3 1 * x 5 (-1) := by
        calc x 5 1 * w23
            = x 5 1 * (x 5 (-1) * x 3 1 * x 5 (-1)) := by
              rw [← nu_w23_neg]
          _ = x 5 1 * x 5 (-1) * (x 3 1 * x 5 (-1)) := by
              group
          _ = x 3 1 * x 5 (-1) := by
              rw [x_add, show (1 : ℤ) + -1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, 1) : Letter) (Or.inl rfl)
        w23 w23_mem_closure w23Conj w23_conj_letter w23Conj_sign
        vnorm_act_w23 hid1
    · have hid1 : x 5 (-1) * w23⁻¹ = x 3 (-1) * x 5 1 := by
        calc x 5 (-1) * w23⁻¹
            = x 5 (-1) * (x 5 1 * x 3 (-1) * x 5 1) := by
              rw [← nu_w23_pos]
          _ = x 5 (-1) * x 5 1 * (x 3 (-1) * x 5 1) := by
              group
          _ = x 3 (-1) * x 5 1 := by
              rw [x_add, show (-1 : ℤ) + 1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, -1) : Letter) (Or.inr rfl)
        w23⁻¹ (Subgroup.inv_mem _ w23_mem_closure) w23ConjInv
        w23inv_hf w23ConjInv_sign vnorm_act_w23inv hid1
    · exact (braid_aligned_35 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (4, 0): Steinberg pair, forward
    rcases exist_st_40 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, c * cp) : Letter) ((0, cp) : Letter)
        ((4, c) : Letter)
        (unit_mul hc hcp) hcp hc ((st_40 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, cp) : Letter) ((5, c * cp) : Letter)
        ((4, c) : Letter)
        hcp (unit_mul hc hcp) hc ((st_40_mid c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, cp) : Letter) ((4, c) : Letter)
        ((5, c * cp) : Letter)
        hcp hc (unit_mul hc hcp) ((st_40_last c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hcp with rfl | rfl
      · have hB : (![1 * vecOf C (act (toSL3 mon) e3) 1, -(1 * vecOf C (act (toSL3 mon) e3) 0),
          vecOf C (act (toSL3 mon) e3) 2] :
          Fin 3 → ℤ) =
          act (toSL3 w) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 2 1 * x 4 c * x 0 (-1) *
          (x 0 1 * x 2 (-1) * x 0 1) =
          x 4 c * x 0 1 := em_40 c 1
        rw [pi_w_pos] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((2, 1) : Letter) ((4, c) : Letter)
          ((0, -1) : Letter)
          (Or.inl rfl) hc (Or.inr rfl)
          w w_mem_closure wConj w_conj_letter wConj_sign
          vnorm_act_w hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![-1 * vecOf C (act (toSL3 mon) e3) 1, -(-1 * vecOf C (act (toSL3 mon) e3) 0),
          vecOf C (act (toSL3 mon) e3) 2] :
          Fin 3 → ℤ) =
          act (toSL3 w⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_winv_vec]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 2 (-1) * x 4 c * x 0 1 *
          (x 0 (-1) * x 2 1 * x 0 (-1)) =
          x 4 c * x 0 (-1) := em_40 c (-1)
        rw [pi_w_neg] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((2, -1) : Letter) ((4, c) : Letter)
          ((0, 1) : Letter)
          (Or.inr rfl) hc (Or.inl rfl)
          w⁻¹ (Subgroup.inv_mem _ w_mem_closure) wConjInv winv_hf
          wConjInv_sign vnorm_act_winv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (4, 1): braid pair, reversed
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (braid_aligned_41 1 (Or.inl rfl) _ hviolC hsideC).elim
    · have hid1 : x 1 1 * w13⁻¹ = x 4 1 * x 1 (-1) := by
        calc x 1 1 * w13⁻¹
            = x 1 1 * (x 1 (-1) * x 4 1 * x 1 (-1)) := by
              rw [← pi_w13_neg]
          _ = x 1 1 * x 1 (-1) * (x 4 1 * x 1 (-1)) := by
              group
          _ = x 4 1 * x 1 (-1) := by
              rw [x_add, show (1 : ℤ) + -1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, 1) : Letter) (Or.inl rfl)
        w13⁻¹ (Subgroup.inv_mem _ w13_mem_closure) w13ConjInv
        w13inv_hf w13ConjInv_sign vnorm_act_w13inv hid1
    · have hid1 : x 1 (-1) * w13 = x 4 (-1) * x 1 1 := by
        calc x 1 (-1) * w13
            = x 1 (-1) * (x 1 1 * x 4 (-1) * x 1 1) := by
              rw [← pi_w13_pos]
          _ = x 1 (-1) * x 1 1 * (x 4 (-1) * x 1 1) := by
              group
          _ = x 4 (-1) * x 1 1 := by
              rw [x_add, show (-1 : ℤ) + 1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((1, -1) : Letter) (Or.inr rfl)
        w13 w13_mem_closure w13Conj w13_conj_letter w13Conj_sign
        vnorm_act_w13 hid1
    · exact (braid_aligned_41 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (4, 2): same read — swap
    have h1 := exist_sr_42 c cp hc hcp _ hviolC hsideC
    exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
      ((2, cp) : Letter) ((4, c) : Letter) hcp hc
      ((x_commute_21_31 cp c).eq)
      (lt_of_lt_of_eq h1 hlamC)
  · -- (4, 3): Steinberg pair, reversed
    rcases exist_st_43 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, -(cp * c)) : Letter) ((3, cp) : Letter)
        ((4, c) : Letter)
        (unit_neg (unit_mul hcp hc)) hcp hc ((stB_43 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hc with rfl | rfl
      · have hB : (![-(vecOf C (act (toSL3 mon) e3) 2),
            vecOf C (act (toSL3 mon) e3) 1,
            vecOf C (act (toSL3 mon) e3) 0] : Fin 3 → ℤ) =
            act (toSL3 w13⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13inv_vec]
        simp only [one_mul] at h1 h2
        rw [hB] at h1 h2
        have hem : x 1 1 * x 2 (-cp) * x 4 (-1) * w13⁻¹ = x 4 1 * x 3 cp := by
          have h := emR_43 1 cp (Or.inl rfl)
          rw [show (-(1 * cp) : ℤ) = -cp from by ring] at h
          rw [nu_w13_pos] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((1, 1) : Letter) ((2, -cp) : Letter)
          ((4, -1) : Letter)
          (Or.inl rfl) (unit_neg hcp) (Or.inr rfl)
          w13⁻¹ (Subgroup.inv_mem _ w13_mem_closure) w13ConjInv w13inv_hf w13ConjInv_sign
          vnorm_act_w13inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![vecOf C (act (toSL3 mon) e3) 2,
            vecOf C (act (toSL3 mon) e3) 1,
            -(vecOf C (act (toSL3 mon) e3) 0)] : Fin 3 → ℤ) =
            act (toSL3 w13) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w13]
        simp only [neg_one_mul, neg_neg] at h1 h2
        rw [hB] at h1 h2
        have hem : x 1 (-1) * x 2 cp * x 4 1 * w13 = x 4 (-1) * x 3 cp := by
          have h := emR_43 (-1) cp (Or.inr rfl)
          rw [show (-(-1 * cp) : ℤ) = cp from by ring,
            show (-(-1) : ℤ) = 1 from by norm_num] at h
          rw [nu_w13_neg] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((1, -1) : Letter) ((2, cp) : Letter)
          ((4, 1) : Letter)
          (Or.inr rfl) hcp (Or.inl rfl)
          w13 w13_mem_closure w13Conj w13_conj_letter w13Conj_sign
          vnorm_act_w13 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (4, 4): same family
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (same_aligned_4 1 (Or.inl rfl) _ hviolC hsideC).elim
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ 1)
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ (-1))
    · exact (same_aligned_4 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (4, 5): same write
    rcases exist_sw_45 c cp hc hcp _ hviolC hsideC with
      h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
        ((5, cp) : Letter) ((4, c) : Letter) hcp hc
        ((x_commute_31_32 c cp).eq.symm) (lt_of_lt_of_eq h1 hlamC)
    · have hs := sand0_conj (-(c * cp)) c
      rw [neg_neg] at hs
      have he : -(-(c * cp) * c) = cp := by
        rcases hc with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, -(c * cp)) : Letter) ((4, c) : Letter)
        ((0, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hc (unit_mul hc hcp)
        (hs.trans ((x_commute_31_32 c cp).eq.symm))
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · have hs := sand2_conj (-(c * cp)) cp
      rw [neg_neg] at hs
      have he : -(-(c * cp) * cp) = c := by
        rcases hcp with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, -(c * cp)) : Letter) ((5, cp) : Letter)
        ((2, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hcp (unit_mul hc hcp)
        hs
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (5, 0): same read — swap
    have h1 := exist_sr_50 c cp hc hcp _ hviolC hsideC
    exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
      ((0, cp) : Letter) ((5, c) : Letter) hcp hc
      ((x_commute_12_32 cp c).eq)
      (lt_of_lt_of_eq h1 hlamC)
  · -- (5, 1): Steinberg pair, reversed
    rcases exist_st_51 c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, -(cp * c)) : Letter) ((1, cp) : Letter)
        ((5, c) : Letter)
        (unit_neg (unit_mul hcp hc)) hcp hc ((stB_51 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hc with rfl | rfl
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0,
            -(vecOf C (act (toSL3 mon) e3) 2),
            vecOf C (act (toSL3 mon) e3) 1] : Fin 3 → ℤ) =
            act (toSL3 w23⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23inv_vec]
        simp only [one_mul] at h1 h2
        rw [hB] at h1 h2
        have hem : x 3 1 * x 0 (-cp) * x 5 (-1) * w23⁻¹ = x 5 1 * x 1 cp := by
          have h := emR_51 1 cp (Or.inl rfl)
          rw [show (-(1 * cp) : ℤ) = -cp from by ring] at h
          rw [nu_w23_pos] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((3, 1) : Letter) ((0, -cp) : Letter)
          ((5, -1) : Letter)
          (Or.inl rfl) (unit_neg hcp) (Or.inr rfl)
          w23⁻¹ (Subgroup.inv_mem _ w23_mem_closure) w23ConjInv w23inv_hf w23ConjInv_sign
          vnorm_act_w23inv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![vecOf C (act (toSL3 mon) e3) 0,
            vecOf C (act (toSL3 mon) e3) 2,
            -(vecOf C (act (toSL3 mon) e3) 1)] : Fin 3 → ℤ) =
            act (toSL3 w23) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w23]
        simp only [neg_one_mul, neg_neg] at h1 h2
        rw [hB] at h1 h2
        have hem : x 3 (-1) * x 0 cp * x 5 1 * w23 = x 5 (-1) * x 1 cp := by
          have h := emR_51 (-1) cp (Or.inr rfl)
          rw [show (-(-1 * cp) : ℤ) = cp from by ring,
            show (-(-1) : ℤ) = 1 from by norm_num] at h
          rw [nu_w23_neg] at h
          exact h
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((3, -1) : Letter) ((0, cp) : Letter)
          ((5, 1) : Letter)
          (Or.inr rfl) hcp (Or.inl rfl)
          w23 w23_mem_closure w23Conj w23_conj_letter w23Conj_sign
          vnorm_act_w23 hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (5, 2): Steinberg pair, forward
    rcases exist_st_52' c cp hc hcp _ hviolC hsideC with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, c * cp) : Letter) ((2, cp) : Letter)
        ((5, c) : Letter)
        (unit_mul hc hcp) hcp hc ((st_52 c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, cp) : Letter) ((4, c * cp) : Letter)
        ((5, c) : Letter)
        hcp (unit_mul hc hcp) hc ((st_52_mid c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, cp) : Letter) ((5, c) : Letter)
        ((4, c * cp) : Letter)
        hcp hc (unit_mul hc hcp) ((st_52_last c cp).symm)
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · rcases hcp with rfl | rfl
      · have hB : (![-(1 * vecOf C (act (toSL3 mon) e3) 1), 1 * vecOf C (act (toSL3 mon) e3) 0,
          vecOf C (act (toSL3 mon) e3) 2] :
          Fin 3 → ℤ) =
          act (toSL3 w⁻¹) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_winv_vec]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 0 1 * x 5 c * x 2 (-1) *
          (x 2 1 * x 0 (-1) * x 2 1) =
          x 5 c * x 2 1 := em_52 c 1
        rw [nu_w_pos] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((0, 1) : Letter) ((5, c) : Letter)
          ((2, -1) : Letter)
          (Or.inl rfl) hc (Or.inr rfl)
          w⁻¹ (Subgroup.inv_mem _ w_mem_closure) wConjInv winv_hf
          wConjInv_sign vnorm_act_winv hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
      · have hB : (![-(-1 * vecOf C (act (toSL3 mon) e3) 1), -1 * vecOf C (act (toSL3 mon) e3) 0,
          vecOf C (act (toSL3 mon) e3) 2] :
          Fin 3 → ℤ) =
          act (toSL3 w) (vecOf C (act (toSL3 mon) e3)) := by
          rw [act_w]
          refine vec3_ext ?_ ?_ ?_ <;> simp
        rw [hB] at h1 h2
        have hem : x 0 (-1) * x 5 c * x 2 1 *
          (x 2 (-1) * x 0 1 * x 2 (-1)) =
          x 5 c * x 2 (-1) := em_52 c (-1)
        rw [nu_w_neg] at hem
        exact route_triple_emit V mon hmon hU hex A C _ _ hsplit hAlen
          ((0, -1) : Letter) ((5, c) : Letter)
          ((2, 1) : Letter)
          (Or.inr rfl) hc (Or.inl rfl)
          w w_mem_closure wConj w_conj_letter wConj_sign
          vnorm_act_w hem
          (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (5, 3): braid pair, reversed
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (braid_aligned_53 1 (Or.inl rfl) _ hviolC hsideC).elim
    · have hid1 : x 3 1 * w23⁻¹ = x 5 1 * x 3 (-1) := by
        calc x 3 1 * w23⁻¹
            = x 3 1 * (x 3 (-1) * x 5 1 * x 3 (-1)) := by
              rw [← pi_w23_neg]
          _ = x 3 1 * x 3 (-1) * (x 5 1 * x 3 (-1)) := by
              group
          _ = x 5 1 * x 3 (-1) := by
              rw [x_add, show (1 : ℤ) + -1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, 1) : Letter) (Or.inl rfl)
        w23⁻¹ (Subgroup.inv_mem _ w23_mem_closure) w23ConjInv
        w23inv_hf w23ConjInv_sign vnorm_act_w23inv hid1
    · have hid1 : x 3 (-1) * w23 = x 5 (-1) * x 3 1 := by
        calc x 3 (-1) * w23
            = x 3 (-1) * (x 3 1 * x 5 (-1) * x 3 1) := by
              rw [← pi_w23_pos]
          _ = x 3 (-1) * x 3 1 * (x 5 (-1) * x 3 1) := by
              group
          _ = x 5 (-1) * x 3 1 := by
              rw [x_add, show (-1 : ℤ) + 1 = 0 from by ring, x_zero,
                one_mul]
      exact route_single_emit V mon hmon hU hex A C _ _ hsplit hAlen
        ((3, -1) : Letter) (Or.inr rfl)
        w23 w23_mem_closure w23Conj w23_conj_letter w23Conj_sign
        vnorm_act_w23 hid1
    · exact (braid_aligned_53 (-1) (Or.inr rfl) _ hviolC hsideC).elim
  · -- (5, 4): same write
    rcases exist_sw_54 c cp hc hcp _ hviolC hsideC with
      h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact route_pair V mon hmon hU hex A C _ _ hsplit hAlen
        ((4, cp) : Letter) ((5, c) : Letter) hcp hc
        ((x_commute_31_32 cp c).eq) (lt_of_lt_of_eq h1 hlamC)
    · have hs := sand2_conj (-(c * cp)) c
      rw [neg_neg] at hs
      have he : -(-(c * cp) * c) = cp := by
        rcases hc with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((2, -(c * cp)) : Letter) ((5, c) : Letter)
        ((2, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hc (unit_mul hc hcp)
        (hs.trans ((x_commute_31_32 cp c).eq))
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
    · have hs := sand0_conj (-(c * cp)) cp
      rw [neg_neg] at hs
      have he : -(-(c * cp) * cp) = c := by
        rcases hcp with rfl | rfl <;> ring
      rw [he] at hs
      exact route_triple V mon hmon hU hex A C _ _ hsplit hAlen
        ((0, -(c * cp)) : Letter) ((4, cp) : Letter)
        ((0, c * cp) : Letter)
        (unit_neg (unit_mul hc hcp)) hcp (unit_mul hc hcp)
        hs
        (lt_of_lt_of_eq h1 hlamC) (lt_of_lt_of_eq h2 hlamC)
  · -- (5, 5): same family
    rcases hc with rfl | rfl <;> rcases hcp with rfl | rfl
    · exact (same_aligned_5 1 (Or.inl rfl) _ hviolC hsideC).elim
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ 1)
    · exact route_nil V mon hmon hU hex A C _ _ hsplit hAlen (cancel_pair _ (-1))
    · exact (same_aligned_5 (-1) (Or.inr rfl) _ hviolC hsideC).elim

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
      · push Not at hv
        exact ⟨V, mon, hmon, rfl,
          (mono_iff_no_viol V _).mpr fun j hj => hv j hj⟩

/-- **Injectivity of the matrix model.** -/
theorem toSL3_injective : Function.Injective toSL3 := by
  rw [injective_iff_map_eq_one]
  exact toSL3_ker_eq_bot descent_normal_form

end

end P13DescentMaster
end GroupApproximation
