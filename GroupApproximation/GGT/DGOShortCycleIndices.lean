import GroupApproximation.GGT.DGOFourGonThin

/-!
# From a pair of indices to a short isolating cycle

Every branch of Dahmani--Guirardel--Osin's Case 4 ends the same way: it names two
indices `m ≤ j` into the polygon, checks that the two vertices are within `θ`,
that one of them is at least `θ + 2` from the basepoint, and that
`m + θ + (|w| - j)` is under the target constant.  `short_cycle_of_indices` is
that ending, so a branch has only to produce the indices and the three numerical
facts.

The offset threshold is `θ + 2` **from the basepoint**, not from the far corner
of the component.  The coset being avoided is centred at `v`, and the two ends of
the component are one letter apart, so an offset measured at `θ + 2` along the
side following the component only yields `θ + 1` from `v`.  The construction
therefore offsets at index `θ + 3`; this is the off-by-one that
"changing the enumeration of the sides" hides in the printed proof.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A pair of indices with an offset gives a short isolating cycle.** -/
theorem short_cycle_of_indices (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    {m j θ N : ℕ} (hmj : m ≤ j) (hjw : j ≤ w.length)
    (hd : wordDist D.alphabet.carrier (vertex v w m) (vertex v w j) ≤ θ)
    (hoff : θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w m) ∨
      θ + 2 ≤ wordDist D.alphabet.carrier v (vertex v w j))
    (hN : m + θ + (w.length - j) ≤ N) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length ≤ N ∧ IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
      (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 := by
  obtain ⟨r, hrlet, hrval, hrle, hrcos⟩ := exists_connector D lam v hd hoff
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ :=
    cycle_of_connector D lam v hlet hcl hcomp hiso hmj hjw hrlet hrval hrcos
  exact ⟨q, hq1, hq2, by omega, hq4, hq5, hq6⟩

end OsinComponents
end GGT
end GroupApproximation
