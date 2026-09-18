import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenAtom
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Commuting letters and the middle split (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitGenConj`: `m(x, y) = higmanVCCommon_mk d (FreeGroup.of
(x, y))`.  These helpers let the atom class of `EnvelopeHigmanVCOrbitGenAtom` use an
arbitrary letter `x`, instead of only the head of `List.finRange d`.

* `higmanVCOrbitAll_branch`: words that extend `c j` and `c x` with `j ≠ x` are incomparable.
* `higmanVCOrbitAll_comm`: when the words of `m(x, y)` are incomparable with both words of
  `m(p, q)`, `m(x, y)` lies in the centralizer of `m(p, q)`.  This comes from the conjugation
  relation `higmanVCOrbitGen_conj` and the fixed-cone lemma `vgen_mapsCone_coneSwap_fix`.
* `higmanVCOrbitAll_split_mid`: split `m(v, w)` over `List.finRange d = l₁ ++ x :: l₂`.
* `higmanVCOrbitAll_elim`: a group identity that cancels a pivot which commutes with the
  left-hand factors.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `c j` is not a prefix of `c x` when `j ≠ x`. -/
theorem higmanVCOrbitAll_ne_prefix {d : ℕ} {j x : Fin d} (hj : j ≠ x) (c : List (Fin d)) :
    ¬ c ++ [j] <+: c ++ [x] := fun h =>
  hj (List.cons_prefix_cons.mp ((List.prefix_append_right_inj c).mp h)).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_ne_prefix

/-- Words that extend `c j` and `c x`, with `j ≠ x`, are incomparable. -/
theorem higmanVCOrbitAll_branch {d : ℕ} {j x : Fin d} (hj : j ≠ x) {c u v : List (Fin d)}
    (hu : c ++ [j] <+: u) (hv : c ++ [x] <+: v) : ¬ u <+: v :=
  higmanVCOrbitGen_incomp (higmanVCOrbitAll_ne_prefix hj c)
    (higmanVCOrbitAll_ne_prefix (Ne.symm hj) c) hu hv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_branch

/-- A letter whose words are incomparable with both words of `m(p, q)` commutes with
`m(p, q)`. -/
theorem higmanVCOrbitAll_comm {d : ℕ} {p q x y : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (h1 : ¬ x <+: p) (h2 : ¬ p <+: x)
    (h3 : ¬ x <+: q) (h4 : ¬ q <+: x) (h5 : ¬ y <+: p) (h6 : ¬ p <+: y) (h7 : ¬ y <+: q)
    (h8 : ¬ q <+: y) :
    higmanVCCommon_mk d (FreeGroup.of (x, y)) ∈
      Subgroup.centralizer {higmanVCCommon_mk d (FreeGroup.of (p, q))} := by
  have e := higmanVCOrbitGen_conj hpq hqp (vgen_mapsCone_coneSwap_fix hpq hqp h1 h2 h3 h4)
    (vgen_mapsCone_coneSwap_fix hpq hqp h5 h6 h7 h8) hxy hyx hxy hyx
  refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
  rw [Set.mem_singleton_iff.mp hg]
  exact mul_inv_eq_iff_eq_mul.mp e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_comm

/-- The split of `m(v, w)` over `List.finRange d = l₁ ++ x :: l₂`, with the `x` letter in
the middle. -/
theorem higmanVCOrbitAll_split_mid {d : ℕ} {x : Fin d} {l₁ l₂ : List (Fin d)}
    (hfr : List.finRange d = l₁ ++ x :: l₂) {v w : List (Fin d)} (h1 : ¬ v <+: w)
    (h2 : ¬ w <+: v) :
    higmanVCCommon_mk d (FreeGroup.of (v, w)) =
      higmanVCCommon_mk d ((l₁.map fun j => FreeGroup.of (v ++ [j], w ++ [j])).prod) *
        (higmanVCCommon_mk d (FreeGroup.of (v ++ [x], w ++ [x])) *
          higmanVCCommon_mk d ((l₂.map fun j => FreeGroup.of (v ++ [j], w ++ [j])).prod)) := by
  rw [higmanVCCommon_mk_split h1 h2, higmanVC_splitAll, hfr, List.map_append, List.map_cons,
    List.prod_append, List.prod_cons, map_mul, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_split_mid

/-- Cancelling a pivot `P` that commutes with `A₀ A₁`. -/
theorem higmanVCOrbitAll_elim {G : Type*} [Group G] {P A₀ A₁ B₀ B₁ : G}
    (hc : A₀ * A₁ * P = P * (A₀ * A₁)) :
    P⁻¹ * (A₀ * (A₁ * (P * B₁) * B₀)) = A₀ * A₁ * (B₁ * B₀) :=
  calc P⁻¹ * (A₀ * (A₁ * (P * B₁) * B₀)) = P⁻¹ * (A₀ * A₁ * P) * (B₁ * B₀) := by
        simp only [mul_assoc]
    _ = A₀ * A₁ * (B₁ * B₀) := by rw [hc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_elim

end GroupApproximation.BooneHigman.Metabelian.Envelope
