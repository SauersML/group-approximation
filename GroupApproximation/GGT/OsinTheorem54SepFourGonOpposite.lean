import GroupApproximation.GGT.OsinTheorem54SepFourGonSide
import GroupApproximation.GGT.OsinTheorem54SepCommIndex

/-!
# A component of the fourth side is a component of the quadrilateral

`GGT/OsinTheorem54SepFourGonSide.lean` carries a component of the long side `q`
into the quadrilateral `p ++ q ++ r ++ revWord s`.  This module does the same
for the OTHER long side, and the traversal is what makes it a separate
statement: `s` is read backwards, so its component `[j,l)` occupies the block

  `[|p|+|q|+|r| + (|s|-l), |p|+|q|+|r| + (|s|-j))`

--- entered at the far end `l` and left at the near end `j` --- and the two
maximality clauses are exchanged along the way (`isComp_revWord`).

## The two ends, and why only one of them costs a hypothesis

At the FRONT of the block the letter before the run is the last letter of `r`,
so the run can only fail to be maximal there if it starts at the block's first
index, which is `l = |s|`.  That is excluded by `l < s.length ∨ 0 < r.length`,
the mirror image of the side lemma's own hypothesis: with `r` nonempty the
preceding letter is a base letter and cannot continue an `H_λ`-run.

At the BACK there is nothing to exclude.  The block ends at the end of the whole
word when `j = 0`, and the maximality clause of `IsComp` is stated as an
implication from `k < |w|`, so it is vacuous exactly there.  This asymmetry is
real: the quadrilateral's last letter is the last letter of the polygon, and no
letter follows it to break the run.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A letter of the quadrilateral in the reversed fourth block is a letter of
`revWord s`.**  The index is supplied by an equation, so that the caller never
has to rewrite underneath `getElem`. -/
theorem getElem_fourGon_revs (p q r s : List (RelLetter G Λ)) {n m : ℕ}
    (hm : m < (revWord s).length)
    (hnm : n = p.length + q.length + r.length + m)
    (hn : n < (p ++ q ++ r ++ revWord s).length) :
    (p ++ q ++ r ++ revWord s)[n]'hn = (revWord s)[m]'hm := by
  subst hnm
  have h3 : (p ++ q ++ r).length ≤ p.length + q.length + r.length + m := by
    rw [List.length_append, List.length_append]
    omega
  rw [List.getElem_append_right h3]
  refine getElem_congr_idx ?_
  rw [List.length_append, List.length_append]
  omega

/-- **A component of the fourth side is a component of the quadrilateral**, at
the reflected indices.

The hypothesis `l < s.length ∨ 0 < r.length` is the mirror of the one carried by
`isComp_fourGon_of_isComp_side`, and excludes the same degeneracy: a run that
starts at the very beginning of the reversed block with nothing but `q` before
it, where the polygon component would be strictly longer than the side
component. -/
theorem isComp_fourGon_of_isComp_opposite (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {j l : ℕ}
    (hcomp : IsComp lam s j l) (hl : l < s.length ∨ 0 < r.length) :
    IsComp lam (p ++ q ++ r ++ revWord s)
      (p.length + q.length + r.length + (s.length - l))
      (p.length + q.length + r.length + (s.length - j)) := by
  have hrev := isComp_revWord lam s hcomp
  have hjl : j < l := hcomp.1
  have hls : l ≤ s.length := hcomp.2.1
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  have hrl : (revWord s).length = s.length := length_revWord s
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro n hn1 hn2 hn
    have hm : n - (p.length + q.length + r.length) < (revWord s).length := by
      omega
    rw [getElem_fourGon_revs p q r s hm (by omega) hn]
    exact hrev.2.2.1 (n - (p.length + q.length + r.length)) (by omega)
      (by omega) hm
  · intro n hn hnlen hc
    by_cases hsl : 0 < s.length - l
    · have hm : s.length - l - 1 < (revWord s).length := by omega
      rw [getElem_fourGon_revs p q r s hm (by omega) hnlen] at hc
      exact hrev.2.2.2.1 (s.length - l - 1) (by omega) hm hc
    · have hrpos : 0 < r.length := by
        rcases hl with h | h
        · omega
        · exact h
      obtain ⟨x, hx⟩ :=
        hr _ (getElem_mem_fourGon_r p q r s (by omega) (by omega) hnlen)
      rw [hx] at hc
      exact hc
  · intro hk hc
    have hm : s.length - j < (revWord s).length := by omega
    rw [getElem_fourGon_revs p q r s hm rfl hk] at hc
    exact hrev.2.2.2.2 hm hc

end OsinComponents
end GGT
end GroupApproximation
