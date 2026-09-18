import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.TMachine

/-!
# Loop macros for structured Minsky machines

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  We prove
three loop lemmas for a structured machine, each from hypotheses on the
instructions of a few states:

* `leads_countdown`: a chain of `add` instructions, closed by a jump;
* `leads_loop`: a loop that empties a glass and runs a body once per coin;
* `leads_divide`: a digit counter that splits a glass into quotient and
  remainder by a modulus `m`.

The glass contents after a loop are described pointwise.
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

namespace TMachine

variable {K : ℕ} {σ : Type} (T : TMachine K σ)

/-- A chain of `k` `add` instructions on glass `dst`, closed by a jump through
the empty glass `z` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads_countdown {A : ℕ → σ} {dst z : Fin K} {X : σ} (hzd : z ≠ dst)
    (hA0 : T.δ (A 0) = some (TInstr.test z X X)) (k : ℕ) :
    (∀ j, j < k → T.δ (A (j + 1)) = some (TInstr.add dst (A j))) →
    ∀ g : Fin K → ℕ, g z = 0 →
      ∃ g' : Fin K → ℕ, T.Leads (A k, g) (X, g') ∧ g' dst = g dst + k ∧
        ∀ i, i ≠ dst → g' i = g i := by
  induction k with
  | zero =>
    intro _ g hg
    exact ⟨g, T.leads_of_leads1 (T.leads1_test_zero hA0 hg), rfl, fun _ _ ↦ rfl⟩
  | succ k ih =>
    intro hA g hg
    have hAk : T.δ (A (k + 1)) = some (TInstr.add dst (A k)) := hA k (by omega)
    have h1 := T.leads1_add hAk g
    have hg1 : Function.update g dst (g dst + 1) z = 0 := by
      rw [Function.update_of_ne hzd]
      exact hg
    obtain ⟨g', hl, hd, ho⟩ :=
      ih (fun j hj ↦ hA j (by omega)) (Function.update g dst (g dst + 1)) hg1
    refine ⟨g', T.leads_of_leads1 (T.leads1_trans_leads h1 hl), ?_, ?_⟩
    · rw [hd, Function.update_self]
      omega
    · intro i hi
      rw [ho i hi, Function.update_of_ne hi]

/-- A loop at `L` that empties glass `src`, running a body once per coin, where
the body adds `s` coins to glass `dst` and needs the glass `z` to be empty
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads_loop {L B X : σ} {src dst z : Fin K} {s : ℕ} (hsd : src ≠ dst)
    (hzs : z ≠ src) (hzd : z ≠ dst)
    (hL : T.δ L = some (TInstr.test src B X))
    (hB : ∀ g : Fin K → ℕ, g z = 0 → ∃ g' : Fin K → ℕ, T.Leads (B, g) (L, g') ∧
      g' dst = g dst + s ∧ ∀ i, i ≠ dst → g' i = g i) (x : ℕ) :
    ∀ g : Fin K → ℕ, g src = x → g z = 0 →
      ∃ g' : Fin K → ℕ, T.Leads (L, g) (X, g') ∧ g' src = 0 ∧
        g' dst = g dst + s * x ∧ ∀ i, i ≠ src → i ≠ dst → g' i = g i := by
  induction x with
  | zero =>
    intro g hg _
    refine ⟨g, T.leads_of_leads1 (T.leads1_test_zero hL hg), hg, ?_, fun _ _ _ ↦ rfl⟩
    rw [Nat.mul_zero, Nat.add_zero]
  | succ x ih =>
    intro g hg hgz
    have h1 := T.leads1_test_pos hL hg
    have hz1 : Function.update g src x z = 0 := by
      rw [Function.update_of_ne hzs]
      exact hgz
    obtain ⟨g1, hl1, hd1, ho1⟩ := hB (Function.update g src x) hz1
    have hg1 : g1 src = x := by
      rw [ho1 src hsd, Function.update_self]
    have hgz1 : g1 z = 0 := by
      rw [ho1 z hzd, Function.update_of_ne hzs]
      exact hgz
    obtain ⟨g', hl, hs', hd', ho'⟩ := ih g1 hg1 hgz1
    refine ⟨g', T.leads_trans (T.leads_of_leads1 (T.leads1_trans_leads h1 hl1)) hl,
      hs', ?_, ?_⟩
    · rw [hd', hd1, Function.update_of_ne hsd.symm, Nat.mul_add_one]
      omega
    · intro i hi1 hi2
      rw [ho' i hi1 hi2, ho1 i hi2, Function.update_of_ne hi1]

/-- A digit counter: the states `D r` (`r < m`) count the coins of glass `src`
modulo `m`, and the carry state `Car` adds the quotient to glass `q`.  When
`src` is empty, `D r` exits to `E r` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads_divide {D E : ℕ → σ} {Car : σ} {src q : Fin K} {m : ℕ} (hsq : src ≠ q)
    (hD : ∀ r, r < m →
      T.δ (D r) = some (TInstr.test src (if r + 1 < m then D (r + 1) else Car) (E r)))
    (hCar : T.δ Car = some (TInstr.add q (D 0))) (x : ℕ) :
    ∀ (r : ℕ) (g : Fin K → ℕ), r < m → g src = x →
      ∃ g' : Fin K → ℕ, T.Leads (D r, g) (E ((r + x) % m), g') ∧ g' src = 0 ∧
        g' q = g q + (r + x) / m ∧ ∀ i, i ≠ src → i ≠ q → g' i = g i := by
  induction x with
  | zero =>
    intro r g hr hg
    have hmod : (r + 0) % m = r := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hr]
    have hdiv : (r + 0) / m = 0 := by
      rw [Nat.add_zero, Nat.div_eq_of_lt hr]
    rw [hmod, hdiv]
    exact ⟨g, T.leads_of_leads1 (T.leads1_test_zero (hD r hr) hg), hg, rfl,
      fun _ _ _ ↦ rfl⟩
  | succ x ih =>
    intro r g hr hg
    have h1 := T.leads1_test_pos (hD r hr) hg
    by_cases hr1 : r + 1 < m
    · rw [if_pos hr1] at h1
      have hg1 : Function.update g src x src = x := Function.update_self _ _ _
      obtain ⟨g', hl, hs', hq', ho'⟩ := ih (r + 1) (Function.update g src x) hr1 hg1
      have he : r + 1 + x = r + (x + 1) := by omega
      rw [he] at hl hq'
      refine ⟨g', T.leads_of_leads1 (T.leads1_trans_leads h1 hl), hs', ?_, ?_⟩
      · rw [hq', Function.update_of_ne hsq.symm]
      · intro i hi1 hi2
        rw [ho' i hi1 hi2, Function.update_of_ne hi1]
    · rw [if_neg hr1] at h1
      have h2 := T.leads1_add hCar (Function.update g src x)
      have hm0 : 0 < m := by omega
      have hg2 : Function.update (Function.update g src x) q
          (Function.update g src x q + 1) src = x := by
        rw [Function.update_of_ne hsq, Function.update_self]
      obtain ⟨g', hl, hs', hq', ho'⟩ := ih 0
        (Function.update (Function.update g src x) q (Function.update g src x q + 1)) hm0 hg2
      have hmod : (r + (x + 1)) % m = (0 + x) % m := by
        rw [show r + (x + 1) = 0 + x + m by omega, Nat.add_mod_right]
      have hdiv : (r + (x + 1)) / m = (0 + x) / m + 1 := by
        rw [show r + (x + 1) = 0 + x + m by omega, Nat.add_div_right _ hm0]
      rw [hmod, hdiv]
      refine ⟨g', T.leads_of_leads1 (T.leads1_trans_leads h1
        (T.leads_of_leads1 (T.leads1_trans_leads h2 hl))), hs', ?_, ?_⟩
      · rw [hq', Function.update_self, Function.update_of_ne hsq.symm]
        omega
      · intro i hi1 hi2
        rw [ho' i hi1 hi2, Function.update_of_ne hi2, Function.update_of_ne hi1]

end TMachine

end GroupApproximation.Full.Kharlampovich.MinskySim
