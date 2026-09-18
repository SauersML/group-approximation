import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Commutators of products of fragments

Let `G, N ≤ M`.  `conjCore G N` is the subgroup of elements all of whose `G`-conjugates lie in
`N`; it is normalized by `G` (`conj_mem_conjCore`) and lies in `N` (`mem_of_mem_conjCore`).

`commutator_le_of_fragments`: if every `⁅a, b⁆` with `a, b ∈ G` in a relation `Small a b` has
all its `G`-conjugates in `N`, and any two `g₁, g₂ ∈ G` are products of lists of elements of
`G` that are pairwise `Small`, then `⁅G, G⁆ ≤ N`.

Route: the identities `⁅x * y, z⁆ = x ⁅y, z⁆ x⁻¹ * ⁅x, z⁆` and
`⁅a, b * w⁆ = ⁅a, b⁆ * b ⁅a, w⁆ b⁻¹` expand `⁅l₁.prod, l₂.prod⁆` into `G`-conjugates of the
`⁅a, b⁆`, `a ∈ l₁`, `b ∈ l₂`; `conjCore G N` absorbs these conjugations although `N` itself
is only assumed to be normalized by `⁅G, G⁆` in the applications.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement

variable {M : Type*} [Group M]

/-- The elements all of whose `G`-conjugates lie in `N`. -/
def conjCore (G N : Subgroup M) : Subgroup M where
  carrier := {n | ∀ x ∈ G, x * n * x⁻¹ ∈ N}
  mul_mem' {a b} ha hb := by
    have ha' : ∀ x ∈ G, x * a * x⁻¹ ∈ N := ha
    have hb' : ∀ x ∈ G, x * b * x⁻¹ ∈ N := hb
    show ∀ x ∈ G, x * (a * b) * x⁻¹ ∈ N
    intro x hx
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact N.mul_mem (ha' x hx) (hb' x hx)
  one_mem' := by
    show ∀ x ∈ G, x * 1 * x⁻¹ ∈ N
    intro x _
    have e : x * 1 * x⁻¹ = 1 := by group
    rw [e]
    exact N.one_mem
  inv_mem' {a} ha := by
    have ha' : ∀ x ∈ G, x * a * x⁻¹ ∈ N := ha
    show ∀ x ∈ G, x * a⁻¹ * x⁻¹ ∈ N
    intro x hx
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact N.inv_mem (ha' x hx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.conjCore

theorem mem_conjCore {G N : Subgroup M} {n : M} :
    n ∈ conjCore G N ↔ ∀ x ∈ G, x * n * x⁻¹ ∈ N :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.mem_conjCore

theorem mem_of_mem_conjCore {G N : Subgroup M} {n : M} (h : n ∈ conjCore G N) : n ∈ N := by
  have h1 := mem_conjCore.mp h 1 G.one_mem
  have e : (1 : M) * n * 1⁻¹ = n := by group
  rwa [e] at h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.mem_of_mem_conjCore

theorem conj_mem_conjCore {G N : Subgroup M} {n y : M} (hn : n ∈ conjCore G N) (hy : y ∈ G) :
    y * n * y⁻¹ ∈ conjCore G N := by
  rw [mem_conjCore]
  intro x hx
  have e : x * (y * n * y⁻¹) * x⁻¹ = (x * y) * n * (x * y)⁻¹ := by group
  rw [e]
  exact mem_conjCore.mp hn _ (G.mul_mem hx hy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.conj_mem_conjCore

theorem commutatorElement_mul_right_eq (a b w : M) :
    ⁅a, b * w⁆ = ⁅a, b⁆ * (b * ⁅a, w⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutatorElement_mul_right_eq

theorem commutatorElement_mul_left_eq (x y z : M) :
    ⁅x * y, z⁆ = (x * ⁅y, z⁆ * x⁻¹) * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutatorElement_mul_left_eq

theorem commutatorElement_list_prod_right_mem {G N : Subgroup M} (a : M) (l : List M)
    (h : ∀ b ∈ l, b ∈ G ∧ ⁅a, b⁆ ∈ conjCore G N) : ⁅a, l.prod⁆ ∈ conjCore G N := by
  induction l with
  | nil =>
    rw [List.prod_nil, commutatorElement_one_right]
    exact (conjCore G N).one_mem
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    rw [List.prod_cons, commutatorElement_mul_right_eq]
    exact (conjCore G N).mul_mem hb.2
      (conj_mem_conjCore (ih fun c hc => h c (List.mem_cons_of_mem b hc)) hb.1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutatorElement_list_prod_right_mem

theorem commutatorElement_list_prod_mem {G N : Subgroup M} (Small : M → M → Prop)
    (hbase : ∀ a ∈ G, ∀ b ∈ G, Small a b → ⁅a, b⁆ ∈ conjCore G N) (l₂ : List M)
    (hl₂ : ∀ b ∈ l₂, b ∈ G) (l₁ : List M) (hl₁ : ∀ a ∈ l₁, a ∈ G)
    (hs : ∀ a ∈ l₁, ∀ b ∈ l₂, Small a b) : ⁅l₁.prod, l₂.prod⁆ ∈ conjCore G N := by
  induction l₁ with
  | nil =>
    rw [List.prod_nil, commutatorElement_one_left]
    exact (conjCore G N).one_mem
  | cons a l ih =>
    have ha : a ∈ G := hl₁ a List.mem_cons_self
    rw [List.prod_cons, commutatorElement_mul_left_eq]
    refine (conjCore G N).mul_mem (conj_mem_conjCore ?_ ha) ?_
    · exact ih (fun c hc => hl₁ c (List.mem_cons_of_mem a hc))
        (fun c hc => hs c (List.mem_cons_of_mem a hc))
    · exact commutatorElement_list_prod_right_mem a l₂ fun b hb =>
        ⟨hl₂ b hb, hbase a ha b (hl₂ b hb) (hs a List.mem_cons_self b hb)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutatorElement_list_prod_mem

/-- **Fragmentation.**  Pairwise small fragments whose commutators have all `G`-conjugates in
`N` force `⁅G, G⁆ ≤ N`. -/
theorem commutator_le_of_fragments (G N : Subgroup M) (Small : M → M → Prop)
    (hbase : ∀ a ∈ G, ∀ b ∈ G, Small a b → ∀ x ∈ G, x * ⁅a, b⁆ * x⁻¹ ∈ N)
    (hfrag : ∀ g₁ ∈ G, ∀ g₂ ∈ G, ∃ l₁ l₂ : List M, (∀ a ∈ l₁, a ∈ G) ∧ (∀ b ∈ l₂, b ∈ G) ∧
      l₁.prod = g₁ ∧ l₂.prod = g₂ ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, Small a b) :
    ⁅G, G⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨l₁, l₂, hl₁, hl₂, hp₁, hp₂, hs⟩ := hfrag g₁ hg₁ g₂ hg₂
  rw [← hp₁, ← hp₂]
  exact mem_of_mem_conjCore (commutatorElement_list_prod_mem Small
    (fun a ha b hb hab => mem_conjCore.mpr (hbase a ha b hb hab)) l₂ hl₂ l₁ hl₁ hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutator_le_of_fragments

end GroupApproximation.BooneHigman.Metabelian.Envelope
