import Mathlib.Tactic.Group
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.FiveStepCentralLeavittSpread
import GroupApproximation.PropertyTT.RingHypotheses
import GroupApproximation.Meta.AxiomGuard

/-!
# Centrality from one nonzero root coefficient, over a sandwich-divisible ring (sk-leavitt-37, 1)

Let `R` be a ring in which every nonzero `a` admits `u a v = 1`
(`HasSingleSandwichDivision R`; for example `L = L_{𝔽₂}(1,2)`).  Let `n ≥ 3`.  This module proves,
with no further hypothesis, the following (`fiveStepK2Central_mem_center_of_conj_commute`).

  If `k ∈ St_n(R)` and some root element `x_{ij}(a)` with `a ≠ 0` commutes with every conjugate
  `g k g⁻¹` of `k`, then `k` is central in `St_n(R)`.

No hypothesis `k ∈ K₂(n, R)` is needed.

## Route

* `Cₖ = {g | ∀ h, g` commutes with `h k h⁻¹}` is a *normal* subgroup of `St_n(R)`
  (`fiveStepK2CentralConjCentralizer`).  It is the centralizer of the normal closure of `k`.
* It contains `x_{ij}(a)`.  Two-sided spreading (`fiveStepCentralLeavitt_map_x_mul_mul`) gives
  `x_{ij}(u a v) = x_{ij}(1) ∈ Cₖ`.
* A normal subgroup containing `x_{ij}(1)` is everything (`fiveStepCentral_mem_of_normal`).  So
  every `g` commutes with `1 · k · 1⁻¹ = k`.

The coefficient `a` may depend on `k`, and so may the root `(i, j)`.  Compare
`fiveStepCentral_K2_le_center_of_commute`, which needs the coefficient `1` and one root uniformly
for all of `K₂(n, R)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

section Conj

variable {G : Type*} [Group G]

/-- The elements commuting with every conjugate of `k`: the centralizer of the normal closure
of `k`. -/
def fiveStepK2CentralConjCentralizer (k : G) : Subgroup G where
  carrier := {g | ∀ h : G, Commute (h * k * h⁻¹) g}
  mul_mem' := by
    intro a b ha hb h
    exact (ha h).mul_right (hb h)
  one_mem' := by
    intro h
    exact Commute.one_right _
  inv_mem' := by
    intro a ha h
    exact (ha h).inv_right

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralConjCentralizer

theorem fiveStepK2CentralConjCentralizer_mem_iff {k g : G} :
    g ∈ fiveStepK2CentralConjCentralizer k ↔ ∀ h : G, Commute (h * k * h⁻¹) g :=
  Iff.rfl

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralConjCentralizer_mem_iff

/-- The centralizer of all conjugates of `k` is normal. -/
instance fiveStepK2CentralConjCentralizer_normal (k : G) :
    (fiveStepK2CentralConjCentralizer k).Normal where
  conj_mem n hn c := by
    rw [fiveStepK2CentralConjCentralizer_mem_iff] at hn ⊢
    intro h
    have e := (hn (c⁻¹ * h)).conj c
    have hc : c * (c⁻¹ * h * k * (c⁻¹ * h)⁻¹) * c⁻¹ = h * k * h⁻¹ := by group
    rw [hc] at e
    exact e

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralConjCentralizer_normal

/-- An element commuting with every conjugate of `k` in particular commutes with `k`. -/
theorem fiveStepK2CentralConjCentralizer_commute {k g : G}
    (hg : g ∈ fiveStepK2CentralConjCentralizer k) : Commute k g := by
  have e := fiveStepK2CentralConjCentralizer_mem_iff.mp hg 1
  rw [one_mul, inv_one, mul_one] at e
  exact e

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2CentralConjCentralizer_commute

end Conj

/-- **Centrality from one nonzero root coefficient**, over any sandwich-divisible ring, for
`n ≥ 3`: if `x_{ij}(a)` with `a ≠ 0` commutes with every conjugate of `k`, then `k` is central in
`St_n(R)`. -/
theorem fiveStepK2Central_mem_center_of_conj_commute {R : Type*} [Ring R]
    (hR : GroupApproximation.HasSingleSandwichDivision R) {n : ℕ} (hn : 3 ≤ n) {i j : Fin n}
    (hij : i ≠ j) {a : R} (ha : a ≠ 0) (k : SteinbergGroup (Fin n) R)
    (h : ∀ g : SteinbergGroup (Fin n) R, Commute (g * k * g⁻¹) (x i j hij a)) :
    k ∈ Subgroup.center (SteinbergGroup (Fin n) R) := by
  obtain ⟨m, him, hjm⟩ := fiveStepCentral_exists_third hn i j
  obtain ⟨u, v, huv⟩ := hR a ha
  have hk0 : x i j hij a ∈ (QuotientGroup.mk' (fiveStepK2CentralConjCentralizer k)).ker := by
    rw [QuotientGroup.ker_mk']
    exact fiveStepK2CentralConjCentralizer_mem_iff.mpr h
  have e := fiveStepCentralLeavitt_map_x_mul_mul
    (QuotientGroup.mk' (fiveStepK2CentralConjCentralizer k)) hij him hjm
    (MonoidHom.mem_ker.mp hk0) u v
  rw [huv] at e
  have hk1 : x i j hij (1 : R) ∈ (QuotientGroup.mk' (fiveStepK2CentralConjCentralizer k)).ker :=
    MonoidHom.mem_ker.mpr e
  rw [QuotientGroup.ker_mk'] at hk1
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := fiveStepCentral_mem_of_normal hn (fiveStepK2CentralConjCentralizer k) hij hk1 g
  exact (fiveStepK2CentralConjCentralizer_commute hg).eq.symm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2Central_mem_center_of_conj_commute

/-- **`K₂(n, R)` is central as soon as each of its elements has one nonzero root coefficient
commuting with all its conjugates**, over any sandwich-divisible ring, for `n ≥ 3`.  The root and
the coefficient may depend on the element. -/
theorem fiveStepK2Central_K2_le_center_of_someRoot {R : Type*} [Ring R]
    (hR : GroupApproximation.HasSingleSandwichDivision R) {n : ℕ} (hn : 3 ≤ n)
    (h : ∀ k ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R,
      ∃ (i j : Fin n) (hij : i ≠ j) (a : R), a ≠ 0 ∧
        ∀ g : SteinbergGroup (Fin n) R, Commute (g * k * g⁻¹) (x i j hij a)) :
    BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R) := by
  intro k hk
  obtain ⟨i, j, hij, a, ha, hc⟩ := h k hk
  exact fiveStepK2Central_mem_center_of_conj_commute hR hn hij ha k hc

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepK2Central_K2_le_center_of_someRoot

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
