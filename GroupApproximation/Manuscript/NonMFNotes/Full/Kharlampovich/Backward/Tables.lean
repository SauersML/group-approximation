import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.Ops

/-!
# The tables of the letters `a_i`, `a'_i` in the KMS model

Input for the "if" direction of KMS Theorem `tmm`(b) (`l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

On an active class, the letter `a_i` (and `ã_i`) acts by the table `tA`, its inverse by
`tAi`, the letter `a'_i` (and `ã'_i`) by `tAp` and its inverse by `tApi`.  Writing
`u_s = v[n ↦ s]`, the new values at `(v, c)` are:

* `tA`:   `z1 ↦ φ u_1 + φ u_2 + φ u_3 + φ σc`, `z2 ↦ φ u_1 + φ u_2`, `z3 ↦ φ u_1`;
* `tAi`:  `z1 ↦ φ u_3`, `z2 ↦ φ u_2 + φ u_3`, `z3 ↦ φ u_1 + φ u_2 + φ σc`;
* `tAp`:  `z1 ↦ φ u_2 + φ u_3 + φ σc`, `z2 ↦ φ u_1`, `z3 ↦ φ u_1 + φ u_3`;
* `tApi`: `z1 ↦ φ u_2`, `z2 ↦ φ u_1 + φ u_2 + φ u_3 + φ σc`, `z3 ↦ φ u_2 + φ u_3`.

This file checks the finite identities between the tables: the inverse pairs,
the commutation of `tA` with `tAp`, and `tAp = tA + id`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

/-- The table of `a_i` (KMS `l789`). -/
def tA : Tab :=
  ⟨fun t s ↦ Tri.sel t (Tri.sel s 1 1 1) (Tri.sel s 1 1 0) (Tri.sel s 1 0 0),
    fun t ↦ Tri.sel t 1 0 0⟩

/-- The table of `a_i⁻¹` (KMS `l789`). -/
def tAi : Tab :=
  ⟨fun t s ↦ Tri.sel t (Tri.sel s 0 0 1) (Tri.sel s 0 1 1) (Tri.sel s 1 1 0),
    fun t ↦ Tri.sel t 0 0 1⟩

/-- The table of `a'_i` (KMS `l789`). -/
def tAp : Tab :=
  ⟨fun t s ↦ Tri.sel t (Tri.sel s 0 1 1) (Tri.sel s 1 0 0) (Tri.sel s 1 0 1),
    fun t ↦ Tri.sel t 1 0 0⟩

/-- The table of `(a'_i)⁻¹` (KMS `l789`). -/
def tApi : Tab :=
  ⟨fun t s ↦ Tri.sel t (Tri.sel s 0 1 0) (Tri.sel s 1 1 1) (Tri.sel s 0 1 1),
    fun t ↦ Tri.sel t 0 1 0⟩

theorem tA_tAi (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    tAi.app t (fun s ↦ tA.app s g (h s)) (tA.app t h y) = g t := by
  cases t <;> simp only [Tab.app, tA, tAi, Tri.sel_z1, Tri.sel_z2, Tri.sel_z3] <;> grind

theorem tAi_tA (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    tA.app t (fun s ↦ tAi.app s g (h s)) (tAi.app t h y) = g t := by
  cases t <;> simp only [Tab.app, tA, tAi, Tri.sel_z1, Tri.sel_z2, Tri.sel_z3] <;> grind

theorem tAp_tApi (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    tApi.app t (fun s ↦ tAp.app s g (h s)) (tAp.app t h y) = g t := by
  cases t <;> simp only [Tab.app, tAp, tApi, Tri.sel_z1, Tri.sel_z2, Tri.sel_z3] <;> grind

theorem tApi_tAp (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    tAp.app t (fun s ↦ tApi.app s g (h s)) (tApi.app t h y) = g t := by
  cases t <;> simp only [Tab.app, tAp, tApi, Tri.sel_z1, Tri.sel_z2, Tri.sel_z3] <;> grind

/-- The tables of `a_i` and `a'_i` commute. -/
theorem tA_tAp_comm (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    tA.app t (fun s ↦ tAp.app s g (h s)) (tAp.app t h y) =
      tAp.app t (fun s ↦ tA.app s g (h s)) (tA.app t h y) := by
  cases t <;> simp only [Tab.app, tA, tAp, Tri.sel_z1, Tri.sel_z2, Tri.sel_z3] <;> grind

theorem tAp_tA_comm (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    tAp.app t (fun s ↦ tA.app s g (h s)) (tA.app t h y) =
      tA.app t (fun s ↦ tAp.app s g (h s)) (tAp.app t h y) :=
  (tA_tAp_comm t g h y).symm

/-- A table commutes with itself. -/
theorem tab_comm_self (T : Tab) (t : Tri) (g h : Tri → ZMod 2) (y : ZMod 2) :
    T.app t (fun s ↦ T.app s g (h s)) (T.app t h y) =
      T.app t (fun s ↦ T.app s g (h s)) (T.app t h y) := rfl

/-- `a'_i = a_i + 1` on active classes (the table form of KMS G5 b), G3 a)). -/
theorem tAp_eq_add (t : Tri) (g : Tri → ZMod 2) (y : ZMod 2) :
    tAp.app t g y = tA.app t g y + g t := by
  cases t <;> simp only [Tab.app, tA, tAp, Tri.sel_z1, Tri.sel_z2, Tri.sel_z3] <;> grind

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
