import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllFamEq
import GroupApproximation.Meta.AxiomGuard

/-!
# The path-atom class passes the pivot (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitAllFamEq`, with `|b| = |a| + 1`.

* `higmanVCOrbitAll_fam_mem_S`: `m(a p, b p y y) · t ∈ S` for every word `p` and letter `y`.
* `higmanVCOrbitAll_Fam`: the class `u · m(a p, b p y y) · (t v t⁻¹)` with `u, v ∈ U`.
  `higmanVCOrbitAll_FamCls` adds its twist `t⁻¹ h⁻¹ t⁻¹`.
* `higmanVCOrbitAll_famCls_mem_S`: every `h` in the class has `h t ∈ S`.
* `higmanVCOrbitAll_famCls_of_cls`: the all-letter atom class (`p = [x]`, `y = x`) lies
  inside the path-atom class.

In the single-swap coordinates `m(a e, b e')` with `k = |e'| - |e|`, the family covers all
`k = 2` swaps with `e' = e y y`.  Its twist covers the matching `k = -2` swaps.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The path atom passes the pivot.**  `m(a p, b p y y) t ∈ S`. -/
theorem higmanVCOrbitAll_fam_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (p : List (Fin d)) (y : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y] ++ [y])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rw [higmanVCOrbitAll_fam_eq hab hba p y]
  refine higmanVCTreeNFWitPivot_S_mul_U ?_ (higmanVCTreeNF_letter_mem ?_)
  · exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem,
      higmanVCOrbitAll_CP a b p y, higmanVCOrbitAll_CP_isAC hab hba p y, _,
      (higmanVCTreeNFWitPivot_H d _).mul_mem
        ((higmanVCTreeNFWitPivot_H d _).inv_mem (higmanVCOrbitAll_L_mem hab hba p y))
        (higmanVCOrbitAll_PtP_mem hab hba p y),
      1, (higmanVCTreeNF_U d).one_mem, by rw [one_mul, mul_one]⟩
  · simp only [List.length_append, List.length_singleton]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_fam_mem_S

/-- **The path-atom class**: `h = u · m(a p, b p y y) · (t v t⁻¹)` with `u, v ∈ U`. -/
def higmanVCOrbitAll_Fam (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ u ∈ higmanVCTreeNF_U d, ∃ p : List (Fin d), ∃ y : Fin d, ∃ v ∈ higmanVCTreeNF_U d,
    h = u * higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y] ++ [y])) *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_Fam

/-- Every element of the path-atom class passes the pivot. -/
theorem higmanVCOrbitAll_fam_class_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitAll_Fam d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u, hu, p, y, v, hv, rfl⟩ := hh
  have e : u * higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y] ++ [y])) *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      u * (higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y] ++ [y])) *
        higmanVCCommon_mk d (FreeGroup.of (a, b))) * v := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U
    (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitAll_fam_mem_S hab hba hlen p y)) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_fam_class_mem_S

/-- The path-atom class together with its twists `t⁻¹ h⁻¹ t⁻¹`. -/
def higmanVCOrbitAll_FamCls (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  higmanVCOrbitAll_Fam d a b h ∨
    higmanVCOrbitAll_Fam d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_FamCls

/-- **Class discharge.**  Every `h` in the path-atom class or its twist has `h t ∈ S`. -/
theorem higmanVCOrbitAll_famCls_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitAll_FamCls d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rcases hh with hh | hh
  · exact higmanVCOrbitAll_fam_class_mem_S hab hba hlen hh
  · have e : h * higmanVCCommon_mk d (FreeGroup.of (a, b)) =
        ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ *
            higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ := by
      group
    rw [e]
    exact higmanVCOrbit_inv_mem_S (higmanVCOrbitAll_fam_class_mem_S hab hba hlen hh)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_famCls_mem_S

/-- The all-letter atom class is the path-atom class at `p = [x]`, `y = x`. -/
theorem higmanVCOrbitAll_fam_of_atom {d : ℕ} {a b : List (Fin d)} {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitAll_Atom d a b h) : higmanVCOrbitAll_Fam d a b h := by
  obtain ⟨u, hu, x, v, hv, e⟩ := hh
  exact ⟨u, hu, [x], x, v, hv, e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_fam_of_atom

/-- `higmanVCOrbitAll_Cls` lies inside `higmanVCOrbitAll_FamCls`. -/
theorem higmanVCOrbitAll_famCls_of_cls {d : ℕ} {a b : List (Fin d)} {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitAll_Cls d a b h) : higmanVCOrbitAll_FamCls d a b h :=
  hh.imp higmanVCOrbitAll_fam_of_atom higmanVCOrbitAll_fam_of_atom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_famCls_of_cls

end GroupApproximation.BooneHigman.Metabelian.Envelope
