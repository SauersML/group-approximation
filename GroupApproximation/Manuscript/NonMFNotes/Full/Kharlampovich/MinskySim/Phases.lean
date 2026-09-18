import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.States
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Minsky

/-!
# The phases of one simulated modular step

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  We run
the simulating machine `tm mm` through the three phases of a modular step:

* `leads_division`: from `divA 0` with `α`, `β` in glasses `0`, `1`, reach the
  dispatch state for the digits of `α` and `β`, with the quotients in glasses
  `2`, `3`;
* `leads_right`: from `mulR c`, write `U·m² + c` into `α` and `V` into `β`;
* `leads_left`: from `trL c`, write `U` into `α` and `V·m² + c` into `β`.

The glass contents are tracked by the predicate `Gl`.
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

open GroupApproximation.BooneGroup

/-- The glasses hold `a, b, u, v` and glass `4` is empty (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
structure Gl (g : Fin 5 → ℕ) (a b u v : ℕ) : Prop where
  /-- Glass `0`. -/
  h0 : g 0 = a
  /-- Glass `1`. -/
  h1 : g 1 = b
  /-- Glass `2`. -/
  h2 : g 2 = u
  /-- Glass `3`. -/
  h3 : g 3 = v
  /-- Glass `4`. -/
  h4 : g 4 = 0

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne01 : (0 : Fin 5) ≠ 1 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne02 : (0 : Fin 5) ≠ 2 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne03 : (0 : Fin 5) ≠ 3 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne04 : (0 : Fin 5) ≠ 4 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne12 : (1 : Fin 5) ≠ 2 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne13 : (1 : Fin 5) ≠ 3 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne14 : (1 : Fin 5) ≠ 4 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne23 : (2 : Fin 5) ≠ 3 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne24 : (2 : Fin 5) ≠ 4 := by decide

/-- Distinct glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem ne34 : (3 : Fin 5) ≠ 4 := by decide

/-- The initial glasses of a code (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem gl_init (a b : ℕ) : Gl (Minsky.initGlasses 5 a b) a b 0 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Glasses holding `a, b, 0, 0` are initial glasses (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem eq_init_of_gl {g : Fin 5 → ℕ} {a b : ℕ} (hg : Gl g a b 0 0) :
    g = Minsky.initGlasses 5 a b := by
  funext i
  match i with
  | ⟨0, _⟩ => exact hg.h0
  | ⟨1, _⟩ => exact hg.h1
  | ⟨2, _⟩ => exact hg.h2
  | ⟨3, _⟩ => exact hg.h3
  | ⟨4, _⟩ => exact hg.h4
  | ⟨n + 5, h⟩ => exact absurd h (by omega)

/-- Empty glasses (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem eq_zero_of_gl {g : Fin 5 → ℕ} (hg : Gl g 0 0 0 0) : g = fun _ ↦ 0 := by
  funext i
  match i with
  | ⟨0, _⟩ => exact hg.h0
  | ⟨1, _⟩ => exact hg.h1
  | ⟨2, _⟩ => exact hg.h2
  | ⟨3, _⟩ => exact hg.h3
  | ⟨4, _⟩ => exact hg.h4
  | ⟨n + 5, h⟩ => exact absurd h (by omega)

variable (mm : ModularMachine)

/-- The division phase: split `α` and `β` into digits and quotients (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads_division {α β : ℕ} {g : Fin 5 → ℕ} (hg : Gl g α β 0 0) :
    ∃ g' : Fin 5 → ℕ, (tm mm).Leads (St.divA (ix mm 0), g)
      (St.disp (ix mm (α % mm.size)) (ix mm (β % mm.size)), g') ∧
      Gl g' 0 0 (α / mm.size) (β / mm.size) := by
  obtain ⟨g1, hl1, hs1, hq1, ho1⟩ := (tm mm).leads_divide
    (D := fun r ↦ St.divA (ix mm r)) (E := fun r ↦ St.divB (ix mm r) (ix mm 0))
    (Car := St.carA) (src := (0 : Fin 5)) (q := (2 : Fin 5)) (m := mm.size) ne02
    (fun r hr ↦ delta_divA mm hr) (delta_carA mm) α 0 g mm.size_pos hg.h0
  have hα : 0 + α = α := Nat.zero_add α
  rw [hα] at hl1 hq1
  have hb1 : g1 1 = β := (ho1 1 ne01.symm ne12).trans hg.h1
  obtain ⟨g2, hl2, hs2, hq2, ho2⟩ := (tm mm).leads_divide
    (D := fun r ↦ St.divB (ix mm (α % mm.size)) (ix mm r))
    (E := fun r ↦ St.disp (ix mm (α % mm.size)) (ix mm r))
    (Car := St.carB (ix mm (α % mm.size))) (src := (1 : Fin 5)) (q := (3 : Fin 5))
    (m := mm.size) ne13 (fun r hr ↦ delta_divB mm (α % mm.size) hr)
    (delta_carB mm (α % mm.size)) β 0 g1 mm.size_pos hb1
  have hβ : 0 + β = β := Nat.zero_add β
  rw [hβ] at hl2 hq2
  refine ⟨g2, (tm mm).leads_trans hl1 hl2, ⟨(ho2 0 ne01 ne03).trans hs1, hs2, ?_, ?_, ?_⟩⟩
  · have e1 := ho2 2 ne12.symm ne23
    have e2 := hg.h2
    omega
  · have e1 := ho1 3 ne03.symm ne23.symm
    have e2 := hg.h3
    omega
  · have e1 := ho2 4 ne14.symm ne34.symm
    have e2 := ho1 4 ne04.symm ne24.symm
    have e3 := hg.h4
    omega

/-- The right phase: from `mulR c`, write `U·m² + c` into `α` and `V` into `β`
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads_right {u v c : ℕ} (hc : c ≤ mm.size ^ 2) {g : Fin 5 → ℕ} (hg : Gl g 0 0 u v) :
    ∃ g' : Fin 5 → ℕ, (tm mm).Leads (St.mulR (ix mm c), g) (St.divA (ix mm 0), g') ∧
      Gl g' (u * mm.size ^ 2 + c) v 0 0 := by
  have hB : ∀ g : Fin 5 → ℕ, g 4 = 0 → ∃ g' : Fin 5 → ℕ,
      (tm mm).Leads (St.addR (ix mm c) (ix mm (mm.size ^ 2)), g) (St.mulR (ix mm c), g') ∧
      g' 0 = g 0 + mm.size ^ 2 ∧ ∀ i, i ≠ 0 → g' i = g i :=
    (tm mm).leads_countdown (A := fun j ↦ St.addR (ix mm c) (ix mm j)) (dst := (0 : Fin 5))
      (z := (4 : Fin 5)) (X := St.mulR (ix mm c)) ne04.symm (delta_addR_zero mm (ix mm c))
      (mm.size ^ 2) (fun j hj ↦ delta_addR_succ mm (ix mm c) (j := j) (Nat.succ_le_of_lt hj))
  obtain ⟨g1, hl1, hs1, hd1, ho1⟩ := (tm mm).leads_loop (L := St.mulR (ix mm c))
    (B := St.addR (ix mm c) (ix mm (mm.size ^ 2))) (X := St.plusR (ix mm c))
    (src := (2 : Fin 5)) (dst := (0 : Fin 5)) (z := (4 : Fin 5)) (s := mm.size ^ 2)
    ne02.symm ne24.symm ne04.symm (delta_mulR mm (ix mm c)) hB u g hg.h2 hg.h4
  have hz1 : g1 4 = 0 := (ho1 4 ne24.symm ne04.symm).trans hg.h4
  obtain ⟨g2, hl2, hd2, ho2⟩ := (tm mm).leads_countdown (A := fun j ↦ St.plusR (ix mm j))
    (dst := (0 : Fin 5)) (z := (4 : Fin 5)) (X := St.trR) ne04.symm (delta_plusR_zero mm) c
    (fun j hj ↦ delta_plusR_succ mm (j := j) (Nat.le_trans (Nat.succ_le_of_lt hj) hc)) g1 hz1
  have hz2 : g2 4 = 0 := (ho2 4 ne04.symm).trans hz1
  have hv2 : g2 3 = v := (ho2 3 ne03.symm).trans ((ho1 3 ne23.symm ne03.symm).trans hg.h3)
  have hB' : ∀ g : Fin 5 → ℕ, g 4 = 0 → ∃ g' : Fin 5 → ℕ,
      (tm mm).Leads (St.trR', g) (St.trR, g') ∧ g' 1 = g 1 + 1 ∧
        ∀ i, i ≠ 1 → g' i = g i :=
    fun g _ ↦ ⟨Function.update g 1 (g 1 + 1),
      (tm mm).leads_of_leads1 ((tm mm).leads1_add (delta_trR' mm) g),
      Function.update_self _ _ _, fun i hi ↦ Function.update_of_ne hi _ _⟩
  obtain ⟨g3, hl3, hs3, hd3, ho3⟩ := (tm mm).leads_loop (L := St.trR) (B := St.trR')
    (X := St.divA (ix mm 0)) (src := (3 : Fin 5)) (dst := (1 : Fin 5)) (z := (4 : Fin 5))
    (s := 1) ne13.symm ne34.symm ne14.symm (delta_trR mm) hB' v g2 hv2 hz2
  refine ⟨g3, (tm mm).leads_trans hl1 ((tm mm).leads_trans hl2 hl3),
    ⟨?_, ?_, (ho3 2 ne23 ne12.symm).trans ((ho2 2 ne02.symm).trans hs1), hs3,
      (ho3 4 ne34.symm ne14.symm).trans hz2⟩⟩
  · have e1 := ho3 0 ne03 ne01
    have e2 := hg.h0
    have e3 : mm.size ^ 2 * u = u * mm.size ^ 2 := Nat.mul_comm _ _
    omega
  · have e1 := ho2 1 ne01.symm
    have e2 := ho1 1 ne12 ne01.symm
    have e3 := hg.h1
    omega

/-- The left phase: from `trL c`, write `U` into `α` and `V·m² + c` into `β`
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads_left {u v c : ℕ} (hc : c ≤ mm.size ^ 2) {g : Fin 5 → ℕ} (hg : Gl g 0 0 u v) :
    ∃ g' : Fin 5 → ℕ, (tm mm).Leads (St.trL (ix mm c), g) (St.divA (ix mm 0), g') ∧
      Gl g' u (v * mm.size ^ 2 + c) 0 0 := by
  have hB : ∀ g : Fin 5 → ℕ, g 4 = 0 → ∃ g' : Fin 5 → ℕ,
      (tm mm).Leads (St.trL' (ix mm c), g) (St.trL (ix mm c), g') ∧
      g' 0 = g 0 + 1 ∧ ∀ i, i ≠ 0 → g' i = g i :=
    fun g _ ↦ ⟨Function.update g 0 (g 0 + 1),
      (tm mm).leads_of_leads1 ((tm mm).leads1_add (delta_trL' mm (ix mm c)) g),
      Function.update_self _ _ _, fun i hi ↦ Function.update_of_ne hi _ _⟩
  obtain ⟨g1, hl1, hs1, hd1, ho1⟩ := (tm mm).leads_loop (L := St.trL (ix mm c))
    (B := St.trL' (ix mm c)) (X := St.mulL (ix mm c)) (src := (2 : Fin 5))
    (dst := (0 : Fin 5)) (z := (4 : Fin 5)) (s := 1) ne02.symm ne24.symm ne04.symm
    (delta_trL mm (ix mm c)) hB u g hg.h2 hg.h4
  have hz1 : g1 4 = 0 := (ho1 4 ne24.symm ne04.symm).trans hg.h4
  have hv1 : g1 3 = v := (ho1 3 ne23.symm ne03.symm).trans hg.h3
  have hB2 : ∀ g : Fin 5 → ℕ, g 4 = 0 → ∃ g' : Fin 5 → ℕ,
      (tm mm).Leads (St.addL (ix mm c) (ix mm (mm.size ^ 2)), g) (St.mulL (ix mm c), g') ∧
      g' 1 = g 1 + mm.size ^ 2 ∧ ∀ i, i ≠ 1 → g' i = g i :=
    (tm mm).leads_countdown (A := fun j ↦ St.addL (ix mm c) (ix mm j)) (dst := (1 : Fin 5))
      (z := (4 : Fin 5)) (X := St.mulL (ix mm c)) ne14.symm (delta_addL_zero mm (ix mm c))
      (mm.size ^ 2) (fun j hj ↦ delta_addL_succ mm (ix mm c) (j := j) (Nat.succ_le_of_lt hj))
  obtain ⟨g2, hl2, hs2, hd2, ho2⟩ := (tm mm).leads_loop (L := St.mulL (ix mm c))
    (B := St.addL (ix mm c) (ix mm (mm.size ^ 2))) (X := St.plusL (ix mm c))
    (src := (3 : Fin 5)) (dst := (1 : Fin 5)) (z := (4 : Fin 5)) (s := mm.size ^ 2)
    ne13.symm ne34.symm ne14.symm (delta_mulL mm (ix mm c)) hB2 v g1 hv1 hz1
  have hz2 : g2 4 = 0 := (ho2 4 ne34.symm ne14.symm).trans hz1
  obtain ⟨g3, hl3, hd3, ho3⟩ := (tm mm).leads_countdown (A := fun j ↦ St.plusL (ix mm j))
    (dst := (1 : Fin 5)) (z := (4 : Fin 5)) (X := St.divA (ix mm 0)) ne14.symm
    (delta_plusL_zero mm) c
    (fun j hj ↦ delta_plusL_succ mm (j := j) (Nat.le_trans (Nat.succ_le_of_lt hj) hc)) g2 hz2
  refine ⟨g3, (tm mm).leads_trans hl1 ((tm mm).leads_trans hl2 hl3),
    ⟨?_, ?_, (ho3 2 ne12.symm).trans ((ho2 2 ne23 ne12.symm).trans hs1),
      (ho3 3 ne13.symm).trans hs2, (ho3 4 ne14.symm).trans hz2⟩⟩
  · have e1 := ho3 0 ne01
    have e2 := ho2 0 ne03 ne01
    have e3 := hg.h0
    omega
  · have e1 := ho1 1 ne12 ne01.symm
    have e2 := hg.h1
    have e3 : mm.size ^ 2 * v = v * mm.size ^ 2 := Nat.mul_comm _ _
    omega

end GroupApproximation.Full.Kharlampovich.MinskySim
