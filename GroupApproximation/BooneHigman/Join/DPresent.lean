import GroupApproximation.BooneHigman.Join.DClose
import GroupApproximation.BooneHigman.Join.DMonoPhi

/-!
# The all-swaps relators present `V_d`, for every `d ≥ 2` (lane bh-pal-met-join)

`higmanVC_ker_le_all`: `ker (higmanVC_evalAll d) ≤ normalClosure (higmanVC_rels d ⊤)` for all
`d > 1`.  This is half (1) of the transfer (`EnvelopeHigmanVCAllReduce`), unconditionally.

* `mk_deep_eq`: the `K`-fold split of `ℓ(x, y)` is `∏_{|w| = K} ℓ(x w, y w)`.
* `mul_jL_memD`: right multiplication by a letter keeps the form `f · σ`, `f ∈ PhiD`,
  `σ ∈ jH L` for a code `L`.  Split the letter below the depth of `L` and use `procL`.
* `N_kerD`: a form `f · σ` acting trivially is `1`.  Its two parts act monotonically, so
  `σ` permutes its cones monotonically and is `1`; then `f = 1` by `PhiD_faithful`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- The words of length `K`. -/
def wordsD (n : ℕ) : ℕ → List (List (Fin (n + 2)))
  | 0 => [[]]
  | K + 1 => (List.finRange (n + 2)).flatMap fun a => (wordsD n K).map (a :: ·)

#audit_axioms GroupApproximation.BooneHigman.Join.wordsD

theorem length_of_mem_wordsD : ∀ {K : ℕ} {w : List (Fin (n + 2))}, w ∈ wordsD n K → w.length = K
  | 0, w, h => by
    have : w = [] := by simpa [wordsD] using h
    rw [this]; rfl
  | K + 1, w, h => by
    simp only [wordsD, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, -, w', hw', rfl⟩ := h
    rw [List.length_cons, length_of_mem_wordsD hw']

#audit_axioms GroupApproximation.BooneHigman.Join.length_of_mem_wordsD

theorem wordsD_pairwise : ∀ K : ℕ, (wordsD n K).Pairwise (· ≠ ·)
  | 0 => List.pairwise_singleton _ _
  | K + 1 => by
    rw [wordsD, List.pairwise_flatMap]
    refine ⟨fun a _ => (wordsD_pairwise K).map _ fun u v h e => h (List.cons_injective e), ?_⟩
    refine (List.nodup_finRange (n + 2)).imp fun hab x hx y hy e => hab ?_
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
    exact (List.cons_eq_cons.mp e).1

#audit_axioms GroupApproximation.BooneHigman.Join.wordsD_pairwise

theorem prod_flatMap' {G α : Type*} [Monoid G] (f : α → List G) :
    ∀ l : List α, (l.flatMap f).prod = (l.map fun a => (f a).prod).prod
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.prod_append, prod_flatMap' f l, List.map_cons,
      List.prod_cons]

#audit_axioms GroupApproximation.BooneHigman.Join.prod_flatMap'

/-- **The `K`-fold split of a letter.** -/
theorem mk_deep_eq : ∀ (K : ℕ) (x y : List (Fin (n + 2))),
    higmanVCCommon_mk (n + 2) (higmanVCCommon_deep (n + 2) K x y) =
      ((wordsD n K).map fun w => jL (x ++ w) (y ++ w)).prod
  | 0, x, y => by
    show jL x y = _
    simp [wordsD]
  | K + 1, x, y => by
    rw [higmanVCCommon_deep_succ, map_list_prod, List.map_map, wordsD, List.map_flatMap,
      prod_flatMap']
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [Function.comp_apply, mk_deep_eq K, List.map_map]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    simp

#audit_axioms GroupApproximation.BooneHigman.Join.mk_deep_eq

theorem sep_words {x y : List (Fin (n + 2))} (hxy : Inc x y) {K : ℕ} :
    ((wordsD n K).map fun w => (x ++ w, y ++ w)).Pairwise Sep := by
  rw [List.pairwise_map]
  refine (wordsD_pairwise K).imp_of_mem fun {u v} hu hv huv => ?_
  have hl : u.length = v.length := by
    rw [length_of_mem_wordsD hu, length_of_mem_wordsD hv]
  have huv' : Inc u v :=
    ⟨fun h => huv (h.eq_of_length hl), fun h => huv (h.eq_of_length hl.symm).symm⟩
  exact ⟨⟨fun h => huv'.1 ((List.prefix_append_right_inj x).mp h),
      fun h => huv'.2 ((List.prefix_append_right_inj x).mp h)⟩, hxy.ext u v, hxy.symm.ext u v,
    ⟨fun h => huv'.1 ((List.prefix_append_right_inj y).mp h),
      fun h => huv'.2 ((List.prefix_append_right_inj y).mp h)⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Join.sep_words

/-- The normal forms. -/
def JND (n : ℕ) : Set (higmanVCCommon_Q (n + 2)) :=
  {q | ∃ f ∈ PhiD n, ∃ L, IsCode n L ∧ ∃ σ ∈ jH (n + 2) L.toFinset, q = f * σ}

#audit_axioms GroupApproximation.BooneHigman.Join.JND

theorem one_mem_JND : (1 : higmanVCCommon_Q (n + 2)) ∈ JND n :=
  ⟨1, (PhiD n).one_mem, [[]], IsCode.root, 1, Subgroup.one_mem _, (one_mul 1).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Join.one_mem_JND

/-- **Right multiplication by a letter keeps the normal form.** -/
theorem mul_jL_memD {q : higmanVCCommon_Q (n + 2)} (hq : q ∈ JND n) (x y : List (Fin (n + 2))) :
    q * jL x y ∈ JND n := by
  by_cases h : ¬ x <+: y ∧ ¬ y <+: x
  · obtain ⟨f, hf, L, hL, σ, hσ, rfl⟩ := hq
    obtain ⟨D, -, hD⟩ := hL.cover
    have hps : ∀ P ∈ (wordsD n D).map (fun w => (x ++ w, y ++ w)),
        Inc P.1 P.2 ∧ AtB L P.1 ∧ AtB L P.2 := by
      intro P hP
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hP
      have hl := length_of_mem_wordsD hw
      exact ⟨(show Inc x y from h).ext w w, hD (x ++ w) (by rw [List.length_append, hl]; omega),
        hD (y ++ w) (by rw [List.length_append, hl]; omega)⟩
    obtain ⟨L', hL', f', hf', σ', hσ', e⟩ := procL _ L hL σ hσ hps (sep_words h)
    refine ⟨f * f', (PhiD n).mul_mem hf hf', L', hL', σ', hσ', ?_⟩
    have hd : jL x y = higmanVCCommon_mk (n + 2) (higmanVCCommon_deep (n + 2) D x y) :=
      (higmanVCCommon_mk_deep D h.1 h.2).symm
    have hj : jL x y = (((wordsD n D).map fun w => (x ++ w, y ++ w)).map
        fun P => jL P.1 P.2).prod := by
      rw [hd, mk_deep_eq, List.map_map]
      all_goals rfl
    calc f * σ * jL x y = f * (σ * jL x y) := mul_assoc _ _ _
      _ = f * (f' * σ') := by rw [hj, e]
      _ = f * f' * σ' := (mul_assoc _ _ _).symm
  · rw [jL_comparable h, mul_one]
    exact hq

#audit_axioms GroupApproximation.BooneHigman.Join.mul_jL_memD

theorem mul_mk_memD (g : FreeGroup (List (Fin (n + 2)) × List (Fin (n + 2)))) :
    ∀ q ∈ JND n, q * higmanVCCommon_mk (n + 2) g ∈ JND n := by
  induction g using FreeGroup.induction_on with
  | C1 =>
    intro q hq
    rwa [map_one, mul_one]
  | of p =>
    intro q hq
    exact mul_jL_memD hq p.1 p.2
  | inv_of p _ =>
    intro q hq
    rw [map_inv, show (higmanVCCommon_mk (n + 2) (FreeGroup.of p))⁻¹ = jL p.1 p.2 from
      jL_inv p.1 p.2]
    exact mul_jL_memD hq p.1 p.2
  | mul a b iha ihb =>
    intro q hq
    rw [map_mul, ← mul_assoc]
    exact ihb _ (iha q hq)

#audit_axioms GroupApproximation.BooneHigman.Join.mul_mk_memD

/-- **Every element of `Q` is a normal form.** -/
theorem mem_JND (q : higmanVCCommon_Q (n + 2)) : q ∈ JND n := by
  obtain ⟨g, rfl⟩ := mk_surj q
  have h := mul_mk_memD g 1 one_mem_JND
  rwa [one_mul] at h

#audit_axioms GroupApproximation.BooneHigman.Join.mem_JND

end GroupApproximation.BooneHigman.Join
