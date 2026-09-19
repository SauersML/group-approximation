-- Re-proved in the `GroupApproximation.CharClass` namespace from the paused fleet's
-- `GroupApproximation/AlgTop/ComplexProjectiveCover.lean`, which is red at the pin and owned by no
-- lane of the LIX program.  Lane `cc-projective` owns this copy.
import GroupApproximation.CharClass.ProjectiveSpaceRetract

/-!
# The Mayer–Vietoris cover of `ℂP^{d+1}`, and the base case `ℂP^0`

This file states the open cover of `ℂP^{d+1}` that the cohomology computation runs on,
and disposes of the base case of the induction.

```text
ℂP^{d+1} = chartSet (d+1) ∪ punctured d,
chartSet (d+1) ∩ punctured d = chartSet (d+1) ∖ {basePoint (d+1)}.
```

Both pieces are open, and their homotopy types are already known:

* `CPn.chartHomeo (d+1) : (Fin (d+1) → ℂ) ≃ₜ ↥(chartSet (d+1))` — a convex, hence
  contractible, space;
* `CPn.punctureHomotopyEquiv d : ↥(punctured d) ≃ₕ CP d` — the inductive step;
* the intersection is the chart with its origin removed
  (`CPn.chartPuncturedHomeo`), i.e. `ℂ^{d+1} ∖ {0}`, which is homotopy equivalent to
  `S^{2d+1}`.

The base case is `ℂP^0`, a one-point space (`CPn.subsingleton_CP_zero`).

## Main results

* `CPn.union_eq_univ`, `CPn.inter_eq` — the cover and its intersection;
* `CPn.chartAt_eq_basePoint_iff` — the base point is the origin of the chart;
* `CPn.chartPuncturedHomeo` — the intersection is `ℂ^{d+1} ∖ {0}`;
* `CPn.subsingleton_CP_zero`, `CPn.eq_basePoint_zero` — `ℂP^0` is a point.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Matrix
open GroupApproximation.STW59

namespace CPn

variable {d : ℕ}

/-! ## 1. The base point sits in the chart, at the origin -/

theorem basePoint_mem_chartSet (d : ℕ) : basePoint d ∈ chartSet d := by
  rw [mem_chartSet, basePoint_entry_zero_zero]
  exact one_ne_zero

theorem chartInv_basePoint (d : ℕ) : chartInv (basePoint d) = 0 := by
  funext i
  show entry (basePoint d) i.succ 0 / entry (basePoint d) 0 0 = 0
  rw [basePoint_entry, baseVec_apply_of_ne (Fin.succ_ne_zero i)]
  simp

/-- The base point of `ℂP^d` is the origin of the affine chart. -/
theorem chartAt_eq_basePoint_iff {w : Fin d → ℂ} : chartAt w = basePoint d ↔ w = 0 := by
  constructor
  · intro h
    have h1 : chartInv (chartAt w) = chartInv (basePoint d) := by rw [h]
    rw [chartInv_chartAt, chartInv_basePoint] at h1
    exact h1
  · rintro rfl
    exact chartAt_zero d

/-! ## 2. The cover -/

/-- **The Mayer–Vietoris cover of `ℂP^{d+1}`**: the affine chart together with the
complement of the base point. -/
theorem union_eq_univ (d : ℕ) : chartSet (d + 1) ∪ punctured d = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : entry x 0 0 = 0
  · refine Or.inr ?_
    intro hbase
    rw [hbase, basePoint_entry_zero_zero] at hx
    exact one_ne_zero hx
  · exact Or.inl hx

/-- The two pieces of the cover meet in the chart with its origin removed. -/
theorem inter_eq (d : ℕ) :
    chartSet (d + 1) ∩ punctured d = {x : CP (d + 1) | entry x 0 0 ≠ 0 ∧ x ≠ basePoint (d + 1)} :=
  rfl

theorem isOpen_inter (d : ℕ) : IsOpen (chartSet (d + 1) ∩ punctured d) :=
  isOpen_chartSet.inter isOpen_punctured

/-! ## 3. The intersection is `ℂ^{d+1} ∖ {0}` -/

/-- Nested subtypes of a subspace and of an intersection agree, topologically. -/
def subtypeInterHomeo {X : Type*} [TopologicalSpace X] (s : Set X) (q : X → Prop) :
    {x : ↥s // q (x : X)} ≃ₜ ↥(s ∩ {x | q x}) where
  toFun x := ⟨(x : X), x.1.2, x.2⟩
  invFun y := ⟨⟨(y : X), y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- The affine chart carries the punctured coordinate space onto the intersection of the
Mayer–Vietoris cover. So that intersection is `ℂ^d ∖ {0}`, whose homotopy type is
`S^{2d-1}`. -/
def chartPuncturedHomeo (d : ℕ) :
    {w : Fin d → ℂ // w ≠ 0} ≃ₜ ↥(chartSet d ∩ {x : CP d | x ≠ basePoint d}) :=
  ((chartHomeo d).subtype (p := fun w : Fin d → ℂ => w ≠ 0)
      (q := fun x : ↥(chartSet d) => (x : CP d) ≠ basePoint d)
      (fun w => by
        constructor
        · intro hw hbase
          exact hw (chartAt_eq_basePoint_iff.mp hbase)
        · intro hne hw
          exact hne (by rw [hw]; exact chartAt_zero d))).trans
    (subtypeInterHomeo (chartSet d) (fun x : CP d => x ≠ basePoint d))

/-- The intersection of the Mayer-Vietoris cover of `ℂP^{d+1}`, spelled with `punctured`. -/
theorem inter_eq_setOf (d : ℕ) :
    chartSet (d + 1) ∩ punctured d
      = chartSet (d + 1) ∩ {x : CP (d + 1) | x ≠ basePoint (d + 1)} := rfl

/-! ## 4. The base case: `ℂP^0` is a point -/

theorem entry_zero_zero_eq_one (x : CP 0) : entry x 0 0 = 1 :=
  (Matrix.trace_fin_one (x : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ)).symm.trans (trace_coe x)

theorem eq_basePoint_zero (x : CP 0) : x = basePoint 0 := by
  refine ext fun a b => ?_
  have ha : a = 0 := Fin.ext (by omega)
  have hb : b = 0 := Fin.ext (by omega)
  subst ha; subst hb
  rw [entry_zero_zero_eq_one, basePoint_entry_zero_zero]

instance subsingleton_CP_zero : Subsingleton (CP 0) :=
  ⟨fun x y => by rw [eq_basePoint_zero x, eq_basePoint_zero y]⟩

end CPn

end GroupApproximation.CharClass
