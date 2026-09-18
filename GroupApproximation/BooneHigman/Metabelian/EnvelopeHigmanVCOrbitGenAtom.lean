import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenAC
import GroupApproximation.Meta.AxiomGuard

/-!
# The atom class passes the pivot (lane bh-met-91l)

Notation as in `EnvelopeHigmanVCOrbitGenConj`, with `|b| = |a| + 1`, and `x` the head of
`List.finRange d` (so `x = 0`).

* `higmanVCOrbitGen_L_mem`: `m(a₁, b₂) ∈ H_C` for the atom antichain `C = C a b x`, by the
  split of `m(a₁, b₂)` over the leaves `a₁ i` and `b₂ i`.
* `higmanVCOrbitGen_Pt_mem`: `m(a₂, b₂)⁻¹ t ∈ H_C`.  Split `t = m(a₁, b₁) R₀` and
  `m(a₁, b₁) = m(a₂, b₂) R₁`, peeling `x` first; then `m(a₂, b₂)⁻¹ t = R₁ R₀`, and all
  letters of `R₀, R₁` lie on leaves of `C`.
* `higmanVCOrbitGen_atom_mem_S`: by the atom identity, `m(a₁, b₃) t ∈ S`.  For `a = a' 0`,
  `b = b' 0 0` this is `swap(a0, b000) · t ∈ S` (with `x = 0`).
* `higmanVCOrbitGen_Atom`: the class `u · m(a₁, b₃) · (t v t⁻¹)`, `u, v ∈ U`, and
  `higmanVCOrbitGen_Cls`: the atom class together with its twist `t⁻¹ h⁻¹ t⁻¹`.  Every
  `h` in the class satisfies `h t ∈ S` (`higmanVCOrbitGen_cls_mem_S`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `m(a₁, b₂) ∈ H_C`. -/
theorem higmanVCOrbitGen_L_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (x : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x])) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitGen_C a b x) := by
  have pa1 : a <+: a ++ [x] := List.prefix_append a [x]
  have pb2 : b <+: b ++ [x] ++ [x] := (List.prefix_append b [x]).trans (List.prefix_append _ [x])
  rw [higmanVCCommon_mk_split (higmanVCOrbitGen_incomp hab hba pa1 pb2)
    (higmanVCOrbitGen_incomp hba hab pb2 pa1), higmanVC_splitAll]
  exact higmanVCOrbitGen_split_mem (a ++ [x]) (b ++ [x] ++ [x]) (List.finRange d) fun i _ =>
    higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a1 a b x i)
      (higmanVCOrbitGen_mem_b2 a b x i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_L_mem

/-- `m(a₂, b₂)⁻¹ t ∈ H_C`, for `x` the head of `List.finRange d`. -/
theorem higmanVCOrbitGen_Pt_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {x : Fin d} {tl : List (Fin d)} (hfr : List.finRange d = x :: tl) :
    (higmanVCCommon_mk d (FreeGroup.of (a ++ [x] ++ [x], b ++ [x] ++ [x])))⁻¹ *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitGen_C a b x) := by
  have hx : x ∉ tl := by
    have hnd := List.nodup_finRange d
    rw [hfr] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hne : ∀ j ∈ tl, j ≠ x := fun j hj h => hx (h ▸ hj)
  have pa1 : a <+: a ++ [x] := List.prefix_append a [x]
  have pb1 : b <+: b ++ [x] := List.prefix_append b [x]
  rw [higmanVCOrbitGen_split_head hfr hab hba, higmanVCOrbitGen_split_head hfr
    (higmanVCOrbitGen_incomp hab hba pa1 pb1) (higmanVCOrbitGen_incomp hba hab pb1 pa1),
    mul_assoc, inv_mul_cancel_left]
  refine (higmanVCTreeNFWitPivot_H d _).mul_mem ?_ ?_
  · exact higmanVCOrbitGen_split_mem (a ++ [x]) (b ++ [x]) tl fun j hj =>
      higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a1 a b x j)
        (higmanVCOrbitGen_mem_b1 a b (hne j hj))
  · exact higmanVCOrbitGen_split_mem a b tl fun j hj =>
      higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a0 a b (hne j hj))
        (higmanVCOrbitGen_mem_b0 a b (hne j hj))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_Pt_mem

/-- **The atom passes the pivot.**  `m(a₁, b₃) t ∈ S`. -/
theorem higmanVCOrbitGen_atom_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {x : Fin d} {tl : List (Fin d)}
    (hfr : List.finRange d = x :: tl) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rw [higmanVCOrbitGen_atom_eq hab hba x]
  refine higmanVCTreeNFWitPivot_S_mul_U ?_ (higmanVCTreeNF_letter_mem ?_)
  · exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem,
      higmanVCOrbitGen_C a b x, higmanVCOrbitGen_C_isAC hab hba x, _,
      (higmanVCTreeNFWitPivot_H d _).mul_mem
        ((higmanVCTreeNFWitPivot_H d _).inv_mem (higmanVCOrbitGen_L_mem hab hba x))
        (higmanVCOrbitGen_Pt_mem hab hba hfr),
      1, (higmanVCTreeNF_U d).one_mem, by rw [one_mul, mul_one]⟩
  · simp only [List.length_append, List.length_singleton]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_atom_mem_S

/-- **The atom class**: `h = u · m(a₁, b₃) · (t v t⁻¹)` with `u, v ∈ U`, where `x` is the
head of `List.finRange d`. -/
def higmanVCOrbitGen_Atom (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  ∃ u ∈ higmanVCTreeNF_U d, ∃ x : Fin d, (∃ tl : List (Fin d), List.finRange d = x :: tl) ∧
    ∃ v ∈ higmanVCTreeNF_U d, h = u *
      higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_Atom

/-- Every element of the atom class passes the pivot. -/
theorem higmanVCOrbitGen_atom_class_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitGen_Atom d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u, hu, x, ⟨tl, hfr⟩, v, hv, rfl⟩ := hh
  have e : u * higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)) * v *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      u * (higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
        higmanVCCommon_mk d (FreeGroup.of (a, b))) * v := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [e]
  exact higmanVCTreeNFWitPivot_S_mul_U
    (higmanVCPivotAC_U_mul_S hu (higmanVCOrbitGen_atom_mem_S hab hba hlen hfr)) hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_atom_class_mem_S

/-- The atom class together with its twists `t⁻¹ h⁻¹ t⁻¹`. -/
def higmanVCOrbitGen_Cls (d : ℕ) (a b : List (Fin d)) (h : higmanVCCommon_Q d) : Prop :=
  higmanVCOrbitGen_Atom d a b h ∨
    higmanVCOrbitGen_Atom d a b ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_Cls

/-- **Class discharge.**  Every `h` in the atom class or its twist satisfies `h t ∈ S`. -/
theorem higmanVCOrbitGen_cls_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitGen_Cls d a b h) :
    h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  rcases hh with hh | hh
  · exact higmanVCOrbitGen_atom_class_mem_S hab hba hlen hh
  · have e : h * higmanVCCommon_mk d (FreeGroup.of (a, b)) =
        ((higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ * h⁻¹ *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ *
            higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ := by
      group
    rw [e]
    exact higmanVCOrbit_inv_mem_S (higmanVCOrbitGen_atom_class_mem_S hab hba hlen hh)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_cls_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
