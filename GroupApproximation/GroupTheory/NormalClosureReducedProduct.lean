import GroupApproximation.GroupTheory.NormalClosureProduct
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.Group

/-!
# Reduced finite products in a normal closure

The tree-shaped certificate `IsRelatorProduct` is flattened here into the
ordered list of signed conjugate relators that forms the 2-cell list of an
algebraic van Kampen diagram.  A certificate with the least possible number
of relator occurrences has no nonempty consecutive block whose product is the
identity: deleting such a block would lower its area.
-/

namespace GroupApproximation
namespace RelatorDefectBudget

variable {G : Type*} [Group G]

/-- A conjugate of a defining relator or of its inverse. -/
def IsSignedConjugate (R : Set G) (x : G) : Prop :=
  ∃ c r : G, r ∈ R ∧
    (x = c * r * c⁻¹ ∨ x = c * r⁻¹ * c⁻¹)

namespace IsSignedConjugate

theorem base {R : Set G} {r : G} (hr : r ∈ R) :
    IsSignedConjugate R r := by
  exact ⟨1, r, hr, Or.inl (by simp)⟩

theorem inv {R : Set G} {x : G} (h : IsSignedConjugate R x) :
    IsSignedConjugate R x⁻¹ := by
  obtain ⟨c, r, hr, hx | hx⟩ := h
  · exact ⟨c, r, hr, Or.inr (by rw [hx]; group)⟩
  · exact ⟨c, r, hr, Or.inl (by rw [hx]; group)⟩

theorem conj {R : Set G} {x : G} (h : IsSignedConjugate R x) (d : G) :
    IsSignedConjugate R (d * x * d⁻¹) := by
  obtain ⟨c, r, hr, hx | hx⟩ := h
  · exact ⟨d * c, r, hr, Or.inl (by rw [hx]; group)⟩
  · exact ⟨d * c, r, hr, Or.inr (by rw [hx]; group)⟩

end IsSignedConjugate

/-- Conjugating every factor conjugates the product. -/
theorem prod_map_conj (c : G) : ∀ factors : List G,
    (factors.map fun x => c * x * c⁻¹).prod = c * factors.prod * c⁻¹
  | [] => by simp
  | x :: xs => by
      rw [List.map_cons, List.prod_cons, prod_map_conj]
      change c * x * c⁻¹ * (c * xs.prod * c⁻¹) =
        c * (x * xs.prod) * c⁻¹
      group

/-- Flatten the inductive certificate without changing its relator count. -/
theorem IsRelatorProduct.exists_flatten {R : Set G} {n : ℕ} {w : G}
    (h : IsRelatorProduct R n w) :
    ∃ factors : List G, factors.length = n ∧ factors.prod = w ∧
      ∀ x ∈ factors, IsSignedConjugate R x := by
  induction h with
  | one => exact ⟨[], rfl, by simp, by simp⟩
  | @base r hr =>
      exact ⟨[r], rfl, by simp, by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact IsSignedConjugate.base hr⟩
  | inv h ih =>
      obtain ⟨factors, hlen, hprod, hcells⟩ := ih
      let factors' := (factors.map fun x => x⁻¹).reverse
      refine ⟨factors', ?_, ?_, ?_⟩
      · simp [factors', hlen]
      · dsimp [factors']
        rw [← List.prod_inv_reverse, hprod]
      · intro x hx
        simp only [factors', List.mem_reverse, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact (hcells y hy).inv
  | conj c h ih =>
      obtain ⟨factors, hlen, hprod, hcells⟩ := ih
      let factors' := factors.map fun x => c * x * c⁻¹
      refine ⟨factors', ?_, ?_, ?_⟩
      · simp [factors', hlen]
      · simp only [factors', prod_map_conj, hprod]
      · intro x hx
        simp only [factors', List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact (hcells y hy).conj c
  | mul ha hb iha ihb =>
      obtain ⟨left, hleftLen, hleftProd, hleftCells⟩ := iha
      obtain ⟨right, hrightLen, hrightProd, hrightCells⟩ := ihb
      refine ⟨left ++ right, ?_, ?_, ?_⟩
      · simp [hleftLen, hrightLen]
      · rw [List.prod_append, hleftProd, hrightProd]
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hleftCells x hx
        · exact hrightCells x hx

/-- Build the tree-shaped certificate back from a flat signed-conjugate list. -/
theorem isRelatorProduct_prod_of_signedConjugates {R : Set G} :
    ∀ factors : List G,
      (∀ x ∈ factors, IsSignedConjugate R x) →
        IsRelatorProduct R factors.length factors.prod
  | [], _ => IsRelatorProduct.one
  | x :: xs, hcells => by
      have hx : IsSignedConjugate R x := hcells x (by simp)
      obtain ⟨c, r, hr, hval⟩ := hx
      have htail : IsRelatorProduct R xs.length xs.prod :=
        isRelatorProduct_prod_of_signedConjugates xs fun y hy =>
          hcells y (by simp [hy])
      rcases hval with hval | hval
      · have hhead : IsRelatorProduct R 1 x := by
          rw [hval]
          exact (IsRelatorProduct.base hr).conj c
        simpa only [List.length_cons, List.prod_cons, Nat.one_add] using
          hhead.mul htail
      · have hhead : IsRelatorProduct R 1 x := by
          rw [hval]
          exact (IsRelatorProduct.base hr).inv.conj c
        simpa only [List.length_cons, List.prod_cons, Nat.one_add] using
          hhead.mul htail

/-- A least-area flat product contains no nonempty consecutive trivial block.
This is the exact algebraic reduced-diagram condition. -/
theorem no_trivial_subproduct_of_minimal
    {R : Set G} {n : ℕ} {w : G} {factors : List G}
    (hlen : factors.length = n) (hprod : factors.prod = w)
    (hcells : ∀ x ∈ factors, IsSignedConjugate R x)
    (hminimal : ∀ {m : ℕ}, IsRelatorProduct R m w → n ≤ m) :
    ∀ (pre mid suf : List G),
      factors = pre ++ mid ++ suf → mid ≠ [] → mid.prod ≠ 1 := by
  intro pre mid suf hsplit hmiddle htrivial
  let shorter := pre ++ suf
  have hshortCells : ∀ x ∈ shorter, IsSignedConjugate R x := by
    intro x hx
    apply hcells x
    rw [hsplit]
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_left _ hx)
    · exact List.mem_append_right _ hx
  have hshortProd : shorter.prod = w := by
    rw [hsplit] at hprod
    simp only [shorter, List.prod_append] at hprod ⊢
    rw [htrivial, mul_one] at hprod
    exact hprod
  have hcertificate : IsRelatorProduct R shorter.length w := by
    rw [← hshortProd]
    exact isRelatorProduct_prod_of_signedConjugates shorter hshortCells
  have hle : n ≤ shorter.length := hminimal hcertificate
  have hlt : shorter.length < n := by
    rw [← hlen, hsplit]
    simp only [shorter, List.length_append]
    have : 0 < mid.length := List.length_pos_iff.mpr hmiddle
    omega
  omega

end RelatorDefectBudget
end GroupApproximation
