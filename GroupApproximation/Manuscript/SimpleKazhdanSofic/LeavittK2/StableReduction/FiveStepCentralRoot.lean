import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Subgroup.Center
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# Centrality of `K₂(n, R)` is decided by a single root element (lane sk-leavitt-33c, part 1)

Let `R` be any unital ring, `n ≥ 3` and `i ≠ j` in `Fin n`.  This module proves, with no further
hypothesis, that `K₂(n, R) ≤ Z(St_n(R))` as soon as every `k ∈ K₂(n, R)` commutes with the single
element `x_{ij}(1)` (`fiveStepCentral_K2_le_center_of_commute`).

## Route

* `Z = C(K₂(n, R))` is a normal subgroup of `St_n(R)`, because `K₂(n, R)` is normal
  (Mathlib `Subgroup.normal_centralizer`).
* A normal subgroup of `St_n(R)` containing `x_{ij}(1)` is everything
  (`fiveStepCentral_mem_of_normal`).  In the quotient `St_n(R) ⧸ N` the image of `x_{ij}(1)` is
  trivial, and the Steinberg commutator relation spreads this to every root element
  (`fiveStepCentral_map_x_eq_one`):
  - `x_{ir}(b) = ⁅x_{ij}(1), x_{jr}(b)⁆` for `r ∉ {i, j}`;
  - `x_{ij}(c) = ⁅x_{im}(c), x_{mj}(1)⁆` for a third index `m`;
  - `x_{pq}(c) = ⁅x_{pi}(c), x_{iq}(1)⁆` for `p, q ≠ i`;
  - `x_{pi}(c) = ⁅x_{pm}(c), x_{mi}(1)⁆` for a third index `m ∉ {p, i}`.
  No division in `R` is needed, since the killed coefficient is `1`.  Compare
  `SteinbergGroup.normalClosure_x_eq_top`, which needs strong division and a fifth index.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

/-- Two indices of `Fin n` with `n ≥ 3` leave room for a third. -/
theorem fiveStepCentral_exists_third {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ k : Fin n, i ≠ k ∧ j ≠ k := by
  by_cases a : (i : ℕ) ≠ 0 ∧ (j : ℕ) ≠ 0
  · exact ⟨⟨0, by omega⟩, fun e => a.1 (congrArg Fin.val e), fun e => a.2 (congrArg Fin.val e)⟩
  by_cases b : (i : ℕ) ≠ 1 ∧ (j : ℕ) ≠ 1
  · exact ⟨⟨1, by omega⟩, fun e => b.1 (congrArg Fin.val e), fun e => b.2 (congrArg Fin.val e)⟩
  refine ⟨⟨2, by omega⟩, fun e => ?_, fun e => ?_⟩
  · have e2 : (i : ℕ) = 2 := congrArg Fin.val e
    omega
  · have e2 : (j : ℕ) = 2 := congrArg Fin.val e
    omega

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_exists_third

/-- **Killing `x_{ij}(1)` kills every root element**, over any ring, for `n ≥ 3`. -/
theorem fiveStepCentral_map_x_eq_one {R : Type*} [Ring R] {Q : Type*} [Group Q] {n : ℕ}
    (hn : 3 ≤ n) (φ : SteinbergGroup (Fin n) R →* Q) {i j : Fin n} (hij : i ≠ j)
    (h1 : φ (x i j hij (1 : R)) = 1) (p q : Fin n) (hpq : p ≠ q) (c : R) :
    φ (x p q hpq c) = 1 := by
  -- Row `i`, columns away from `j`.
  have hoff : ∀ (r : Fin n) (hir : i ≠ r) (hjr : j ≠ r) (b : R), φ (x i r hir b) = 1 := by
    intro r hir hjr b
    have e := x_commutator i j r hij hjr hir (1 : R) b
    rw [one_mul] at e
    rw [← e, map_commutatorElement, h1, commutatorElement_one_left]
  -- The whole row `i`.
  have hrow : ∀ (r : Fin n) (hir : i ≠ r) (b : R), φ (x i r hir b) = 1 := by
    intro r hir b
    by_cases hjr : j = r
    · obtain ⟨m, him, hjm⟩ := fiveStepCentral_exists_third hn i j
      have hmr : m ≠ r := fun e => hjm (hjr.trans e.symm)
      have e := x_commutator i m r him hmr hir b (1 : R)
      rw [mul_one] at e
      rw [← e, map_commutatorElement, hoff m him hjm b, commutatorElement_one_left]
    · exact hoff r hir hjr b
  -- Roots `(p, r)` with `p ≠ i` and `r ≠ i`.
  have hmid : ∀ (s r : Fin n) (hsr : s ≠ r) (hsi : s ≠ i) (hri : r ≠ i) (b : R),
      φ (x s r hsr b) = 1 := by
    intro s r hsr hsi hri b
    have e := x_commutator s i r hsi (Ne.symm hri) hsr b (1 : R)
    rw [mul_one] at e
    rw [← e, map_commutatorElement, hrow r (Ne.symm hri) 1, commutatorElement_one_right]
  by_cases hpi : p = i
  · subst hpi
    exact hrow q hpq c
  · by_cases hqi : q = i
    · -- Column `i`.
      obtain ⟨m, hpm, him⟩ := fiveStepCentral_exists_third hn p i
      have hmq : m ≠ q := fun e => him (e.trans hqi).symm
      have e := x_commutator p m q hpm hmq hpq c (1 : R)
      rw [mul_one] at e
      rw [← e, map_commutatorElement, hmid p m hpm hpi (Ne.symm him) c,
        commutatorElement_one_left]
    · exact hmid p q hpq hpi hqi c

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_map_x_eq_one

/-- **A normal subgroup of `St_n(R)` containing `x_{ij}(1)` is everything**, for `n ≥ 3`. -/
theorem fiveStepCentral_mem_of_normal {R : Type*} [Ring R] {n : ℕ} (hn : 3 ≤ n)
    (N : Subgroup (SteinbergGroup (Fin n) R)) [N.Normal] {i j : Fin n} (hij : i ≠ j)
    (h1 : x i j hij (1 : R) ∈ N) (g : SteinbergGroup (Fin n) R) : g ∈ N := by
  have hk1 : x i j hij (1 : R) ∈ (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact h1
  refine PresentedGroup.generated_by _ N ?_ g
  rintro ⟨p, q, hpq, c⟩
  have hk : x p q hpq c ∈ (QuotientGroup.mk' N).ker :=
    MonoidHom.mem_ker.mpr
      (fiveStepCentral_map_x_eq_one hn (QuotientGroup.mk' N) hij (MonoidHom.mem_ker.mp hk1)
        p q hpq c)
  rw [QuotientGroup.ker_mk'] at hk
  exact hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_mem_of_normal

/-- **Centrality of `K₂(n, R)` from one root element**, over any ring, for `n ≥ 3`: if every
`k ∈ K₂(n, R)` commutes with `x_{ij}(1)`, then `K₂(n, R)` is central in `St_n(R)`.  The
centralizer of the normal subgroup `K₂(n, R)` is normal and contains `x_{ij}(1)`. -/
theorem fiveStepCentral_K2_le_center_of_commute {R : Type*} [Ring R] {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j)
    (h : ∀ k ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R, Commute k (x i j hij (1 : R))) :
    BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R) := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hx : x i j hij (1 : R) ∈ Subgroup.centralizer
      (BooneHigman.SteinbergBasic.K2 (Fin n) R : Set (SteinbergGroup (Fin n) R)) :=
    Subgroup.mem_centralizer_iff.mpr fun k' hk' => (h k' hk').eq
  have hg : g ∈ Subgroup.centralizer
      (BooneHigman.SteinbergBasic.K2 (Fin n) R : Set (SteinbergGroup (Fin n) R)) :=
    fiveStepCentral_mem_of_normal hn
      (Subgroup.centralizer
        (BooneHigman.SteinbergBasic.K2 (Fin n) R : Set (SteinbergGroup (Fin n) R))) hij hx g
  exact (Subgroup.mem_centralizer_iff.mp hg k hk).symm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_K2_le_center_of_commute

/-- The converse is immediate, so the single-root condition is equivalent to centrality. -/
theorem fiveStepCentral_commute_of_K2_le_center {R : Type*} [Ring R] {n : ℕ}
    (hC : BooneHigman.SteinbergBasic.K2 (Fin n) R ≤ Subgroup.center (SteinbergGroup (Fin n) R))
    {i j : Fin n} (hij : i ≠ j) :
    ∀ k ∈ BooneHigman.SteinbergBasic.K2 (Fin n) R, Commute k (x i j hij (1 : R)) :=
  fun k hk => (Subgroup.mem_center_iff.mp (hC hk) (x i j hij (1 : R))).symm

#audit_axioms
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.fiveStepCentral_commute_of_K2_le_center

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
