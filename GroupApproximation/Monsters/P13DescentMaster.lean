import GroupApproximation.Monsters.P13Completeness

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
open P13ColumnLift P13ParabolicKernel P13MonomialMachine
open P13DescentCore P13WordDescent P13Completeness

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
