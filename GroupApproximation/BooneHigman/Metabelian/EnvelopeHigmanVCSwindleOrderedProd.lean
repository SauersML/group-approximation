import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleShuffle
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import GroupApproximation.Meta.AxiomGuard

/-!
# Inserting a factor in a sorted noncommutative product

Only factors preceding the inserted element need commute with it. This lets
the canonical code lift use a fixed depth order without imposing commutativity
on shuffles at comparable internal nodes.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higSw_sort_insert {α : Type*} [LinearOrder α] (S : Finset α)
    (a : α) (ha : a ∉ S) :
    (insert a S).sort (· ≤ ·) = List.orderedInsert (· ≤ ·) a (S.sort (· ≤ ·)) := by
  rw [← Finset.cons_eq_insert a S ha]
  change Multiset.sort (a ::ₘ S.val) (· ≤ ·) = _
  rw [← S.sort_eq (· ≤ ·)]
  change (a :: S.sort (· ≤ ·)).mergeSort (· ≤ ·) = _
  rw [List.mergeSort_eq_insertionSort, List.insertionSort_cons,
    (S.pairwise_sort (· ≤ ·)).insertionSort_eq]

theorem higSw_orderedInsert_prod {α G : Type*} [LinearOrder α] [Group G]
    (l : List α) (a : α) (f : α → G)
    (hc : ∀ b ∈ l, b < a → Commute (f a) (f b)) :
    ((List.orderedInsert (· ≤ ·) a l).map f).prod = f a * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons b l ih =>
    by_cases hab : a ≤ b
    · rw [List.orderedInsert_cons_of_le (· ≤ ·) l hab]
      rfl
    · rw [List.orderedInsert_of_not_le (· ≤ ·) l hab]
      simp only [List.map_cons, List.prod_cons]
      rw [ih (fun x hx hxa => hc x (List.mem_cons_of_mem b hx) hxa)]
      rw [← mul_assoc, ← (hc b List.mem_cons_self (lt_of_not_ge hab)).eq, mul_assoc]

/-- Exact insertion in a sorted finite product under the necessary commutation conditions. -/
theorem higSw_sort_prod_insert {α G : Type*} [LinearOrder α] [Group G]
    (S : Finset α) (a : α) (ha : a ∉ S) (f : α → G)
    (hc : ∀ b ∈ S, b < a → Commute (f a) (f b)) :
    (((insert a S).sort (· ≤ ·)).map f).prod =
      f a * ((S.sort (· ≤ ·)).map f).prod := by
  rw [higSw_sort_insert S a ha]
  exact higSw_orderedInsert_prod _ a f
    (fun b hb hba => hc b ((Finset.mem_sort (· ≤ ·)).mp hb) hba)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_sort_prod_insert

end GroupApproximation.BooneHigman.Metabelian.Envelope
