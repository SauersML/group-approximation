import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllPt
import GroupApproximation.Meta.AxiomGuard

/-!
# The all-letter atom class passes the pivot (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitGenAtom`, with `|b| = |a| + 1`.  The file
`EnvelopeHigmanVCOrbitGenAtom` proves the atom statements only for `x` the head of
`List.finRange d`.  Here they hold for **every** letter `x : Fin d`, using
`higmanVCOrbitAll_Pt_mem`.

* `higmanVCOrbitAll_atom_mem_S`: `m(a x, b x x x) · t ∈ S` for every `x`.
* `higmanVCOrbitAll_Atom`: the class `u · m(a x, b x x x) · (t v t⁻¹)` with `u, v ∈ U` and
  any `x`.  `higmanVCOrbitAll_Cls` adds its twist `t⁻¹ h⁻¹ t⁻¹`.
* `higmanVCOrbitAll_cls_mem_S`: every `h` in the class has `h t ∈ S`.
* `higmanVCOrbitAll_cls_of_gen`: the old class `higmanVCOrbitGen_Cls` lies inside the new one.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The atom passes the pivot, for every letter `x`.**  `m(a₁, b₃) t ∈ S`. -/
theorem higmanVCOrbitAll_atom_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (x : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rw [higmanVCOrbitGen_atom_eq hab hba x]
  refine higmanVCTreeNFWitPivot_S_mul_U ?_ (higmanVCTreeNF_letter_mem ?_)
  · exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem,
      higmanVCOrbitGen_C a b x, higmanVCOrbitGen_C_isAC hab hba x, _,
      (higmanVCTreeNFWitPivot_H d _).mul_mem
        ((higmanVCTreeNFWitPivot_H d _).inv_mem (higmanVCOrbitGen_L_mem hab hba x))
        (higmanVCOrbitAll_Pt_mem hab hba x),
      1, (higmanVCTreeNF_U d).one_mem, by rw [one_mul, mul_one]⟩
  · simp only [List.length_append, List.length_singleton]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_atom_mem_S

/-- **The all-letter atom class**: `h = u · m(a₁, b₃) · (t v t⁻¹)` with `u, v ∈ U` and any
letter `x`. -/
def higmanVCOrbitAll_Atom (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ u ∈ higmanVCTreeNF_U d, ∃ x : Fin d, ∃ v ∈ higmanVCTreeNF_U d, h = u *
    higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_Atom

/-- Every element of the all-letter atom class passes the pivot. -/
theorem higmanVCOrbitAll_atom_class_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitAll_Atom d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u, hu, x, v, hv, rfl⟩ := hh
  have e : u * higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      u * (higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
        higmanVCCommon_mk d (FreeGroup.of (a, b))) * v := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U
    (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitAll_atom_mem_S hab hba hlen x)) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_atom_class_mem_S

/-- The all-letter atom class together with its twists `t⁻¹ h⁻¹ t⁻¹`. -/
def higmanVCOrbitAll_Cls (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  higmanVCOrbitAll_Atom d a b h ∨
    higmanVCOrbitAll_Atom d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_Cls

/-- **Class discharge.**  Every `h` in the all-letter atom class or its twist has
`h t ∈ S`. -/
theorem higmanVCOrbitAll_cls_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitAll_Cls d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rcases hh with hh | hh
  · exact higmanVCOrbitAll_atom_class_mem_S hab hba hlen hh
  · have e : h * higmanVCCommon_mk d (FreeGroup.of (a, b)) =
        ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ *
            higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ := by
      group
    rw [e]
    exact higmanVCOrbit_inv_mem_S (higmanVCOrbitAll_atom_class_mem_S hab hba hlen hh)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_cls_mem_S

/-- The head-letter atom class lies inside the all-letter one. -/
theorem higmanVCOrbitAll_atom_of_gen {d : ℕ} {a b : List (Fin d)} {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitGen_Atom d a b h) : higmanVCOrbitAll_Atom d a b h := by
  obtain ⟨u, hu, x, _, v, hv, e⟩ := hh
  exact ⟨u, hu, x, v, hv, e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_atom_of_gen

/-- The head-letter class `higmanVCOrbitGen_Cls` lies inside `higmanVCOrbitAll_Cls`. -/
theorem higmanVCOrbitAll_cls_of_gen {d : ℕ} {a b : List (Fin d)} {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitGen_Cls d a b h) : higmanVCOrbitAll_Cls d a b h :=
  hh.imp higmanVCOrbitAll_atom_of_gen higmanVCOrbitAll_atom_of_gen

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_cls_of_gen

end GroupApproximation.BooneHigman.Metabelian.Envelope
