import GroupApproximation.GGT.OsinTheorem54SepTwoBlockRot

/-!
# Two base-spelled sides carry no component start

`GGT.OsinComponents.two_block_conj_named` bounds both gaps of a matched pair of
blocks and keeps their names, which is what the aligned and mirrored branches of
Olshanskii's step (c) spend: the join consumes the vertex relation
`y * vertex 1 w i = vertex 1 w' j`, and that relation is what the first gap being
trivial SAYS once the gap is known to be
`(vertex 1 s j)⁻¹ * (listVal p * vertex 1 q i)`.  From the existential form the
design still gives `x = 1`, but `x` is then an anonymous element of the ball and
the vertex relation does not follow.  The named form is in
`GGT/OsinTheorem54SepTwoBlockRot.lean`; nothing is restated here.

What is here is the pair of vacuity lemmas its two configuration clauses are met
by whenever the relevant range of the quadrilateral falls inside a base-spelled
side.  A base letter carries no index, and the letter at a component's start
always does, so no component starts there at all.

Neither clause is vacuous in the quadrilateral the long match builds --- there
the first side is followed by a matched prefix, whose block letters lie in both
ranges, and the clauses say the matched pair is INNERMOST.  These two lemmas
close the ranges that do fall inside `p` and `r`: the other-arc clause when the
matched block is the first letter of the long side, and the innermost clause
when it is the last.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **No component of the quadrilateral starts inside a base-spelled first
side.** -/
theorem not_isCompStart_fourGon_p (p q r s : List (RelLetter G Λ)) (lam : Λ)
    (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {o : ℕ} (ho : o < p.length) :
    ¬ IsCompStart lam (p ++ q ++ r ++ revWord s) o := by
  rintro ⟨k, hcomp⟩
  have hov : o < (p ++ q ++ r ++ revWord s).length := by
    rw [length_fourGon]
    omega
  have hc := hcomp.2.2.1 o le_rfl hcomp.1 hov
  obtain ⟨x, hx⟩ := hp _ (getElem_mem_fourGon_p p q r s ho hov)
  rw [hx] at hc
  exact hc

/-- **No component of the quadrilateral starts inside a base-spelled third
side.** -/
theorem not_isCompStart_fourGon_r (p q r s : List (RelLetter G Λ)) (lam : Λ)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {o : ℕ}
    (h1 : p.length + q.length ≤ o) (h2 : o < p.length + q.length + r.length) :
    ¬ IsCompStart lam (p ++ q ++ r ++ revWord s) o := by
  rintro ⟨k, hcomp⟩
  have hov : o < (p ++ q ++ r ++ revWord s).length := by
    rw [length_fourGon]
    omega
  have hc := hcomp.2.2.1 o le_rfl hcomp.1 hov
  obtain ⟨x, hx⟩ := hr _ (getElem_mem_fourGon_r p q r s h1 h2 hov)
  rw [hx] at hc
  exact hc

end OsinComponents
end GGT
end GroupApproximation
