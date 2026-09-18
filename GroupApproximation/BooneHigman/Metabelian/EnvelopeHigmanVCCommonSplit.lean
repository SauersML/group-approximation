import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# All-swaps presentation: deep splitting of letters (lane bh-met-77d)

`higmanVCCommon_Q d` is the quotient of the all-swaps free group by the standard relators
`higmanVC_rels d fun _ => True`, and `higmanVCCommon_mk d` is the quotient map.

In this quotient:

* a comparable letter is trivial (`higmanVCCommon_mk_comparable`);
* every letter is an involution (`higmanVCCommon_mk_inv_of`);
* an incomparable letter `(x, y)` equals its `m`-fold split `higmanVCCommon_deep d m x y`, the
  product of the letters `(x c, y c)` over the words `c` of length `m` (`higmanVCCommon_mk_deep`).

Consequently, an element commuting with every incomparable letter of length `≥ N` commutes with
every letter (`higmanVCCommon_commute_of_letter`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The quotient of the all-swaps free group by the standard relators. -/
abbrev higmanVCCommon_Q (d : ℕ) : Type :=
  FreeGroup (List (Fin d) × List (Fin d)) ⧸
    Subgroup.normalClosure (higmanVC_rels d fun _ => True)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_Q

/-- The quotient map onto `higmanVCCommon_Q d`. -/
noncomputable def higmanVCCommon_mk (d : ℕ) :
    FreeGroup (List (Fin d) × List (Fin d)) →* higmanVCCommon_Q d :=
  QuotientGroup.mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk

/-- An element is killed by the quotient map iff it lies in the normal closure. -/
theorem higmanVCCommon_mk_eq_one_iff {d : ℕ} {t : FreeGroup (List (Fin d) × List (Fin d))} :
    higmanVCCommon_mk d t = 1 ↔ t ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  rw [higmanVCCommon_mk, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_eq_one_iff

/-- Relators are killed by the quotient map. -/
theorem higmanVCCommon_mk_rel {d : ℕ} {t : FreeGroup (List (Fin d) × List (Fin d))}
    (ht : t ∈ higmanVC_rels d fun _ => True) : higmanVCCommon_mk d t = 1 :=
  higmanVCCommon_mk_eq_one_iff.mpr (Subgroup.subset_normalClosure ht)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_rel

/-- A comparable letter is trivial in the quotient. -/
theorem higmanVCCommon_mk_comparable {d : ℕ} {x y : List (Fin d)}
    (h : ¬ (¬ x <+: y ∧ ¬ y <+: x)) : higmanVCCommon_mk d (FreeGroup.of (x, y)) = 1 := by
  refine higmanVCCommon_mk_rel ?_
  rw [higmanVC_rels, Set.mem_setOf_eq]
  exact Or.inl ⟨x, y, trivial, trivial, h, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_comparable

/-- Every letter squares to `1` in the quotient. -/
theorem higmanVCCommon_mk_sq {d : ℕ} (x y : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (x, y)) * higmanVCCommon_mk d (FreeGroup.of (x, y)) = 1 := by
  have h : FreeGroup.of (x, y) * FreeGroup.of (x, y) ∈ higmanVC_rels d fun _ => True := by
    rw [higmanVC_rels, Set.mem_setOf_eq]
    exact Or.inr (Or.inl ⟨x, y, trivial, trivial, rfl⟩)
  have h' := higmanVCCommon_mk_rel h
  rw [map_mul] at h'
  exact h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_sq

/-- The inverse of a letter equals the letter in the quotient. -/
theorem higmanVCCommon_mk_inv_of {d : ℕ} (x y : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (x, y))⁻¹ = higmanVCCommon_mk d (FreeGroup.of (x, y)) := by
  rw [map_inv]
  exact inv_eq_of_mul_eq_one_right (higmanVCCommon_mk_sq x y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_inv_of

/-- An incomparable letter equals its split in the quotient. -/
theorem higmanVCCommon_mk_split {d : ℕ} {x y : List (Fin d)} (h1 : ¬ x <+: y)
    (h2 : ¬ y <+: x) :
    higmanVCCommon_mk d (FreeGroup.of (x, y)) = higmanVCCommon_mk d (higmanVC_splitAll x y) := by
  have h : FreeGroup.of (x, y) * (higmanVC_splitAll x y)⁻¹ ∈ higmanVC_rels d fun _ => True := by
    rw [higmanVC_rels, Set.mem_setOf_eq]
    exact Or.inr (Or.inr (Or.inr ⟨x, y, trivial, trivial, fun _ => ⟨trivial, trivial⟩, h1, h2,
      rfl⟩))
  have h' := higmanVCCommon_mk_rel h
  rw [map_mul, map_inv, mul_inv_eq_one] at h'
  exact h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_split

/-- The `m`-fold split of the letter `(x, y)`: `deep 0 x y = (x, y)` and
`deep (m + 1) x y = ∏_{a} deep m (x a) (y a)`. -/
def higmanVCCommon_deep (d : ℕ) : ℕ → List (Fin d) → List (Fin d) →
    FreeGroup (List (Fin d) × List (Fin d))
  | 0, x, y => FreeGroup.of (x, y)
  | m + 1, x, y =>
    ((List.finRange d).map fun a => higmanVCCommon_deep d m (x ++ [a]) (y ++ [a])).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_deep

theorem higmanVCCommon_deep_zero {d : ℕ} (x y : List (Fin d)) :
    higmanVCCommon_deep d 0 x y = FreeGroup.of (x, y) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_deep_zero

theorem higmanVCCommon_deep_succ {d : ℕ} (m : ℕ) (x y : List (Fin d)) :
    higmanVCCommon_deep d (m + 1) x y =
      ((List.finRange d).map fun a => higmanVCCommon_deep d m (x ++ [a]) (y ++ [a])).prod :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_deep_succ

/-- **Deep splitting.**  An incomparable letter equals its `m`-fold split in the quotient. -/
theorem higmanVCCommon_mk_deep {d : ℕ} (m : ℕ) :
    ∀ {x y : List (Fin d)}, ¬ x <+: y → ¬ y <+: x →
      higmanVCCommon_mk d (higmanVCCommon_deep d m x y) =
        higmanVCCommon_mk d (FreeGroup.of (x, y)) := by
  induction m with
  | zero =>
    intro x y _ _
    rw [higmanVCCommon_deep_zero]
  | succ m ih =>
    intro x y h1 h2
    rw [higmanVCCommon_deep_succ, higmanVCCommon_mk_split h1 h2, higmanVC_splitAll,
      map_list_prod, map_list_prod, List.map_map, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun a _ =>
      ih (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_mk_deep

/-- An element commuting with every incomparable letter of length `≥ N` commutes with every
`m`-fold split of an incomparable letter `(x, y)` with `N ≤ |x| + m` and `N ≤ |y| + m`. -/
theorem higmanVCCommon_commute_deep {d N : ℕ} {z : higmanVCCommon_Q d}
    (hz : ∀ a b : List (Fin d), N ≤ a.length → N ≤ b.length → ¬ a <+: b → ¬ b <+: a →
      Commute z (higmanVCCommon_mk d (FreeGroup.of (a, b)))) (m : ℕ) :
    ∀ {x y : List (Fin d)}, ¬ x <+: y → ¬ y <+: x → N ≤ x.length + m → N ≤ y.length + m →
      Commute z (higmanVCCommon_mk d (higmanVCCommon_deep d m x y)) := by
  induction m with
  | zero =>
    intro x y h1 h2 hx hy
    rw [higmanVCCommon_deep_zero]
    exact hz x y (by omega) (by omega) h1 h2
  | succ m ih =>
    intro x y h1 h2 hx hy
    rw [higmanVCCommon_deep_succ, map_list_prod, List.map_map]
    refine Commute.list_prod_right _ _ fun t ht => ?_
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
    have hxa : N ≤ (x ++ [a]).length + m := by
      rw [List.length_append, List.length_singleton]
      omega
    have hya : N ≤ (y ++ [a]).length + m := by
      rw [List.length_append, List.length_singleton]
      omega
    exact ih (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a) hxa hya

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_commute_deep

/-- **Letters from deep letters.**  An element commuting with every incomparable letter of
length `≥ N` commutes with every letter. -/
theorem higmanVCCommon_commute_of_letter {d N : ℕ} {z : higmanVCCommon_Q d}
    (hz : ∀ a b : List (Fin d), N ≤ a.length → N ≤ b.length → ¬ a <+: b → ¬ b <+: a →
      Commute z (higmanVCCommon_mk d (FreeGroup.of (a, b)))) (u v : List (Fin d)) :
    Commute z (higmanVCCommon_mk d (FreeGroup.of (u, v))) := by
  by_cases h : ¬ u <+: v ∧ ¬ v <+: u
  · rw [← higmanVCCommon_mk_deep N h.1 h.2]
    exact higmanVCCommon_commute_deep hz N h.1 h.2 (Nat.le_add_left N _) (Nat.le_add_left N _)
  · rw [higmanVCCommon_mk_comparable h]
    exact Commute.one_right z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_commute_of_letter

end GroupApproximation.BooneHigman.Metabelian.Envelope
