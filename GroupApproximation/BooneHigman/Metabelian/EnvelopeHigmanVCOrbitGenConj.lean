import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGapReduce
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The atom identity for the pivot (lane bh-met-91l)

Notation: `m(x, y) = higmanVCCommon_mk d (FreeGroup.of (x, y))`, `t = m(a, b)` with `a, b`
incomparable, and for a letter `x : Fin d` write `a₁ = a x`, `a₂ = a x x`, `a₃ = a x x x`
(similarly for `b`).

The four conjugation relations
* `t · m(b₁, a₃) · t⁻¹ = m(a₁, b₃)`,
* `m(b₁, a₂) · m(b₁, a₃) · m(b₁, a₂)⁻¹ = m(a₂, b₂)`,
* `t · m(b₁, a₂) · t⁻¹ = m(a₁, b₂)`,
* `t · m(a₂, b₂) · t⁻¹ = m(b₂, a₂) = m(a₂, b₂)⁻¹`

combine (`higmanVCOrbitGen_key_eq`, a pure group identity) to the **atom identity**
`m(a₁, b₃) · t = m(a₁, b₂)⁻¹ · (m(a₂, b₂)⁻¹ · t) · m(b₁, a₂)`
(`higmanVCOrbitGen_atom_eq`).  The letter `m(b₁, a₂)` is balanced.  The truth of all four
relations and of the atom identity was checked on permutations of words in `V_d`,
`d ∈ {2, 3}`, for several pivots and every `x`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Extending incomparable words keeps them incomparable. -/
theorem higmanVCOrbitGen_incomp {d : ℕ} {x y x' y' : List (Fin d)} (h1 : ¬ x <+: y)
    (h2 : ¬ y <+: x) (hx : x <+: x') (hy : y <+: y') : ¬ x' <+: y' := by
  intro h
  rcases List.prefix_or_prefix_of_prefix (hx.trans h) hy with h' | h'
  · exact h1 h'
  · exact h2 h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_incomp

/-- The conjugation relation, as an equation in `Q`. -/
theorem higmanVCOrbitGen_conj {d : ℕ} {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hmx : MapsCone (coneSwap p q hpq hqp) x x')
    (hmy : MapsCone (coneSwap p q hpq hqp) y y') (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCCommon_mk d (FreeGroup.of (p, q)) * higmanVCCommon_mk d (FreeGroup.of (x, y)) *
        (higmanVCCommon_mk d (FreeGroup.of (p, q)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (x', y')) := by
  have hr := higmanVCCommon_mk_rel
    (higmanVCCommon_conj_mem hpq hqp hmx hmy hxy hyx hxy' hyx')
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
  exact mul_inv_eq_one.mp hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_conj

/-- An incomparable letter is symmetric: `m(y, x) = m(x, y)`. -/
theorem higmanVCOrbitGen_symm {d : ℕ} {x y : List (Fin d)} (h1 : ¬ x <+: y)
    (h2 : ¬ y <+: x) :
    higmanVCCommon_mk d (FreeGroup.of (y, x)) = higmanVCCommon_mk d (FreeGroup.of (x, y)) := by
  have e := higmanVCOrbitGen_conj (d := d) h1 h2 (mapsCone_coneSwap_left h1 h2)
    (mapsCone_coneSwap_right h1 h2) h1 h2 h2 h1
  rw [mul_inv_cancel_right] at e
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_symm

/-- **The key group identity** behind the atom identity. -/
theorem higmanVCOrbitGen_key_eq {G : Type*} [Group G] {t k w h₀ P L : G}
    (e1 : t * k * t⁻¹ = h₀) (e2 : w * k * w⁻¹ = P) (e3 : t * w * t⁻¹ = L)
    (e4 : t * P * t⁻¹ = P⁻¹) : h₀ * t = L⁻¹ * (P⁻¹ * t) * w := by
  subst e1 e2 e3
  rw [← e4]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_key_eq

/-- **The atom identity.**  `m(a₁, b₃) t = m(a₁, b₂)⁻¹ (m(a₂, b₂)⁻¹ t) m(b₁, a₂)`. -/
theorem higmanVCOrbitGen_atom_eq {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (x : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x] ++ [x])) *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      (higmanVCCommon_mk d (FreeGroup.of (a ++ [x], b ++ [x] ++ [x])))⁻¹ *
        ((higmanVCCommon_mk d (FreeGroup.of (a ++ [x] ++ [x], b ++ [x] ++ [x])))⁻¹ *
          higmanVCCommon_mk d (FreeGroup.of (a, b))) *
        higmanVCCommon_mk d (FreeGroup.of (b ++ [x], a ++ [x] ++ [x])) := by
  have pa1 : a <+: a ++ [x] := List.prefix_append a [x]
  have pa2 : a <+: a ++ [x] ++ [x] := pa1.trans (List.prefix_append _ [x])
  have pa3 : a <+: a ++ [x] ++ [x] ++ [x] := pa2.trans (List.prefix_append _ [x])
  have pb1 : b <+: b ++ [x] := List.prefix_append b [x]
  have pb2 : b <+: b ++ [x] ++ [x] := pb1.trans (List.prefix_append _ [x])
  have pb3 : b <+: b ++ [x] ++ [x] ++ [x] := pb2.trans (List.prefix_append _ [x])
  have mL := mapsCone_coneSwap_left hab hba
  have mR := mapsCone_coneSwap_right hab hba
  have i12 := higmanVCOrbitGen_incomp hba hab pb1 pa2
  have i21 := higmanVCOrbitGen_incomp hab hba pa2 pb1
  have i13 := higmanVCOrbitGen_incomp hba hab pb1 pa3
  have i31 := higmanVCOrbitGen_incomp hab hba pa3 pb1
  have j13 := higmanVCOrbitGen_incomp hab hba pa1 pb3
  have j31 := higmanVCOrbitGen_incomp hba hab pb3 pa1
  have j12 := higmanVCOrbitGen_incomp hab hba pa1 pb2
  have j21 := higmanVCOrbitGen_incomp hba hab pb2 pa1
  have j22 := higmanVCOrbitGen_incomp hab hba pa2 pb2
  have k22 := higmanVCOrbitGen_incomp hba hab pb2 pa2
  refine higmanVCOrbitGen_key_eq
    (k := higmanVCCommon_mk d (FreeGroup.of (b ++ [x], a ++ [x] ++ [x] ++ [x]))) ?_ ?_ ?_ ?_
  · exact higmanVCOrbitGen_conj hab hba (mR.append [x])
      (((mL.append [x]).append [x]).append [x]) i13 i31 j13 j31
  · exact higmanVCOrbitGen_conj i12 i21 (mapsCone_coneSwap_left i12 i21)
      ((mapsCone_coneSwap_right i12 i21).append [x]) i13 i31 j22 k22
  · exact higmanVCOrbitGen_conj hab hba (mR.append [x]) ((mL.append [x]).append [x]) i12 i21
      j12 j21
  · exact (higmanVCOrbitGen_conj hab hba ((mL.append [x]).append [x])
      ((mR.append [x]).append [x]) j22 k22 k22 j22).trans ((higmanVCOrbitGen_symm j22 k22).trans
        (inv_eq_of_mul_eq_one_right
          (higmanVCCommon_mk_sq (a ++ [x] ++ [x]) (b ++ [x] ++ [x]))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_atom_eq

end GroupApproximation.BooneHigman.Metabelian.Envelope
