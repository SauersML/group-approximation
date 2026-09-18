import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.Phases
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.Simulation

/-!
# The simulating machine simulates the modular machine

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  The code
of `(α, β)` is the state `divA 0` with `α`, `β` in glasses `0`, `1` and all other
glasses empty.  We check the four conditions of `Simulates`:

* a modular step is simulated by the division phase, the dispatch and the right
  or left phase;
* a stuck configuration with a nonzero digit gives a dispatch state without an
  instruction;
* a stuck configuration with zero digits and a nonzero quotient ends at `stuck`;
* the code of `(0, 0)` reaches `stop` with all glasses empty.
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

open GroupApproximation.BooneGroup

variable (mm : ModularMachine)

/-- The code of a modular configuration (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def code (p : ℕ × ℕ) : St (mm.size ^ 2) × (Fin 5 → ℕ) :=
  (St.divA (ix mm 0), Minsky.initGlasses 5 p.1 p.2)

/-- Codes are not the stop configuration (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem code_ne_stopc (p : ℕ × ℕ) : code mm p ≠ (tm mm).stopc := by
  intro h
  have h1 : (St.divA (ix mm 0) : St (mm.size ^ 2)) = St.stop := congrArg Prod.fst h
  cases h1

/-- Reaching `stuck` gives a non-stop fixed point (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem fixed_of_leads_stuck {c : St (mm.size ^ 2) × (Fin 5 → ℕ)} {g : Fin 5 → ℕ}
    (h : (tm mm).Leads c (St.stuck, g)) :
    ∃ d, (tm mm).Leads c d ∧ (tm mm).next d = d ∧ d ≠ (tm mm).stopc := by
  refine ⟨(St.stuck, g), h,
    (tm mm).next_of_step_none ((tm mm).step_eq_none_of_δ (delta_stuck mm) g), ?_⟩
  intro hd
  have h1 : (St.stuck : St (mm.size ^ 2)) = St.stop := congrArg Prod.fst hd
  cases h1

/-- A modular step is simulated (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem code_step_some (p q : ℕ × ℕ) (hpq : mm.step p = some q) :
    (tm mm).Leads1 (code mm p) (code mm q) := by
  obtain ⟨α, β⟩ := p
  have ha : α % mm.size < mm.size := Nat.mod_lt _ mm.size_pos
  have hb : β % mm.size < mm.size := Nat.mod_lt _ mm.size_pos
  obtain ⟨g1, hl1, hg1⟩ := leads_division mm (gl_init α β)
  rcases hq : mm.quad (α % mm.size) (β % mm.size) with _ | ⟨c, _ | _⟩
  · rw [mm.step_eq_none (α := α) (β := β) hq] at hpq
    cases hpq
  · rw [mm.step_left (α := α) (β := β) hq] at hpq
    have hq' : q = (mm.hi α, mm.hi β * mm.size ^ 2 + c) := (Option.some.inj hpq).symm
    subst hq'
    have hc : c ≤ mm.size ^ 2 := Nat.le_of_lt (mm.quad_lt hq)
    have h1 := (tm mm).leads1_test_zero (delta_disp_false mm ha hb hq) hg1.h4
    obtain ⟨g2, hl2, hg2⟩ := leads_left mm hc hg1
    have he := eq_init_of_gl hg2
    subst he
    exact (tm mm).leads_trans_leads1 hl1 ((tm mm).leads1_trans_leads h1 hl2)
  · rw [mm.step_right (α := α) (β := β) hq] at hpq
    have hq' : q = (mm.hi α * mm.size ^ 2 + c, mm.hi β) := (Option.some.inj hpq).symm
    subst hq'
    have hc : c ≤ mm.size ^ 2 := Nat.le_of_lt (mm.quad_lt hq)
    have h1 := (tm mm).leads1_test_zero (delta_disp_true mm ha hb hq) hg1.h4
    obtain ⟨g2, hl2, hg2⟩ := leads_right mm hc hg1
    have he := eq_init_of_gl hg2
    subst he
    exact (tm mm).leads_trans_leads1 hl1 ((tm mm).leads1_trans_leads h1 hl2)

/-- A number with zero quotient and zero digit is zero (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem eq_zero_of_div_mod {α : ℕ} (hd : α / mm.size = 0) (hm : α % mm.size = 0) : α = 0 := by
  have e := Nat.div_add_mod α mm.size
  rw [hd, hm, Nat.mul_zero] at e
  omega

/-- A stuck nonzero configuration leads to a non-stop fixed point (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem code_step_none (p : ℕ × ℕ) (hp : p ≠ (0, 0)) (hs : mm.step p = none) :
    ∃ d, (tm mm).Leads (code mm p) d ∧ (tm mm).next d = d ∧ d ≠ (tm mm).stopc := by
  obtain ⟨α, β⟩ := p
  have ha : α % mm.size < mm.size := Nat.mod_lt _ mm.size_pos
  have hb : β % mm.size < mm.size := Nat.mod_lt _ mm.size_pos
  obtain ⟨g1, hl1, hg1⟩ := leads_division mm (gl_init α β)
  have hq : mm.quad (α % mm.size) (β % mm.size) = none := by
    rcases hq : mm.quad (α % mm.size) (β % mm.size) with _ | ⟨c, _ | _⟩
    · rfl
    · rw [mm.step_left (α := α) (β := β) hq] at hs
      cases hs
    · rw [mm.step_right (α := α) (β := β) hq] at hs
      cases hs
  by_cases hab : α % mm.size = 0 ∧ β % mm.size = 0
  · obtain ⟨ha0, hb0⟩ := hab
    rw [ha0, hb0] at hl1
    by_cases hu : α / mm.size = 0
    · have hv : β / mm.size ≠ 0 := by
        intro hv
        apply hp
        rw [eq_zero_of_div_mod mm hu ha0, eq_zero_of_div_mod mm hv hb0]
      obtain ⟨w, hw⟩ : ∃ w, β / mm.size = w + 1 := ⟨β / mm.size - 1, by omega⟩
      have h2 := (tm mm).leads1_test_zero (delta_disp_zero mm) (hg1.h2.trans hu)
      have h3 := (tm mm).leads1_test_pos (delta_chk0 mm) (hg1.h3.trans hw)
      exact fixed_of_leads_stuck mm ((tm mm).leads_trans hl1 ((tm mm).leads_of_leads1
        ((tm mm).leads1_trans_leads h2 ((tm mm).leads_of_leads1 h3))))
    · obtain ⟨w, hw⟩ : ∃ w, α / mm.size = w + 1 := ⟨α / mm.size - 1, by omega⟩
      have h2 := (tm mm).leads1_test_pos (delta_disp_zero mm) (hg1.h2.trans hw)
      exact fixed_of_leads_stuck mm ((tm mm).leads_trans hl1 ((tm mm).leads_of_leads1 h2))
  · refine ⟨_, hl1,
      (tm mm).next_of_step_none ((tm mm).step_eq_none_of_δ (delta_disp_none mm ha hb hq hab) g1),
      ?_⟩
    intro hd
    have h1 : (St.disp (ix mm (α % mm.size)) (ix mm (β % mm.size)) : St (mm.size ^ 2)) =
        St.stop := congrArg Prod.fst hd
    cases h1

/-- The code of `(0, 0)` reaches the stop configuration (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem code_halt : (tm mm).Leads (code mm (0, 0)) (tm mm).stopc := by
  obtain ⟨g1, hl1, hg1⟩ := leads_division mm (gl_init 0 0)
  have hz : 0 % mm.size = 0 := Nat.zero_mod _
  have hd : 0 / mm.size = 0 := Nat.zero_div _
  rw [hz] at hl1
  have h2 := (tm mm).leads1_test_zero (delta_disp_zero mm) (hg1.h2.trans hd)
  have h3 := (tm mm).leads1_test_zero (delta_chk0 mm) (hg1.h3.trans hd)
  have hg0 : Gl g1 0 0 0 0 := ⟨hg1.h0, hg1.h1, hg1.h2.trans hd, hg1.h3.trans hd, hg1.h4⟩
  have he := eq_zero_of_gl hg0
  subst he
  exact (tm mm).leads_trans hl1 ((tm mm).leads_of_leads1
    ((tm mm).leads1_trans_leads h2 ((tm mm).leads_of_leads1 h3)))

/-- The simulating machine simulates the modular machine (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem simulates : Simulates mm (tm mm) (code mm) :=
  ⟨code_ne_stopc mm, code_step_some mm, code_step_none mm, code_halt mm⟩

end GroupApproximation.Full.Kharlampovich.MinskySim
