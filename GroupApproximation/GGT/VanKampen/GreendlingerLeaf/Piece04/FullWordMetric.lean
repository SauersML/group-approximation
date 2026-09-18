import GroupApproximation.Algebra.HyperbolicSlimFourPoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the metric half of the full-word branch

This module holds only word-metric geometry: a group `G`, a symmetric generating set `S`, and the
four-point condition at `δ`. Write `d` for `wordDist S`.

## The tripod lemma (`exists_close_between`)

Take points `X, X', Y, Y'`. Let `E = d(X,X') + d(Y,Y') − d(Y,X') − d(X,Y')` and assume `|E| ≤ 2δ`.
Put `t = ⌊(d(X,Y) + d(X,X') − d(Y,X'))/2⌋` and `s = ⌊(d(X,Y) + d(Y,Y') − d(X,Y'))/2⌋`. The triangle
inequality gives `t ≤ d(X,X')` and `s ≤ d(Y,Y')`.

Take `p` between `X` and `X'` with `d(X,p) = t`, and `q` between `Y` and `Y'` with `d(Y,q) = s`
(`Hyperbolic.exists_isBetween`). The four-point condition gives three bounds.

* For `(p, Y, X, X')`: `d(p,Y) + d(X,X') ≤ max(t + d(Y,X'), d(X,X') − t + d(X,Y)) + 2δ`. Since
  `2t ≤ d(X,Y) + d(X,X') − d(Y,X')`, this means `d(p,Y) ≤ d(X,Y) − t + 2δ`.
* For `(q, X, Y, Y')`, in the same way: `d(q,X) ≤ d(X,Y) − s + 2δ`.
* For `(p, q, X, Y)`: `d(p,q) + d(X,Y) ≤ max(t + s, d(p,Y) + d(q,X)) + 2δ`.

Now `2t + 2s ≤ 2d(X,Y) + E ≤ 2d(X,Y) + 2δ`, and `2t + 2s ≥ 2d(X,Y) + E − 2 ≥ 2d(X,Y) − 2δ − 2`.
So `d(p,q) ≤ max(3δ, 7δ + 1) ≤ 8δ + 2`.

## The full-word quadrilateral (`exists_close_of_fullWord`)

Take `A, A', B, B'` with `d(B,A) + d(B',A') < d(A,A') + d(B,B')`. Write `P1 = d(A,A') + d(B,B')`,
`P2 = d(A,B) + d(A',B')` and `P3 = d(A,B') + d(A',B)`. The four-point condition gives
`P1 ≤ max(P2, P3) + 2δ` and `P3 ≤ max(P1, P2) + 2δ = P1 + 2δ`.

* **Case I**, `P1 ≤ P3 + 2δ`: apply the tripod lemma to `(A, A', B, B')`, where `E = P1 − P3`.
* **Case II**, otherwise: `P1 ≤ P2 + 2δ`. Apply the tripod lemma to `(A, A', B', B)`, where
  `E = P1 − P2 ∈ (0, 2δ]`.

Either way some `p` between `A` and `A'` and some `q` between `B'` and `B` satisfy
`d(p,q) ≤ 8δ + 2`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u

open GroupApproximation.WordMetric

/-- A bound by a maximum is a bound by one of its two arguments. -/
theorem fullWord_le_or_le_of_le_max_add {a b c k : ℕ} (h : a ≤ max b c + k) :
    a ≤ b + k ∨ a ≤ c + k := by
  rcases le_total b c with hbc | hbc
  · right
    rw [max_eq_right hbc] at h
    exact h
  · left
    rw [max_eq_left hbc] at h
    exact h

/-- **The tripod lemma.** If the two pairings `d(X,X') + d(Y,Y')` and `d(Y,X') + d(X,Y')` differ by at
most `2δ`, some point between `X` and `X'` is within `8δ + 2` of some point between `Y` and `Y'`. -/
theorem exists_close_between {G : Type u} [Group G] {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic S δ)
    (X X' Y Y' : G)
    (hE1 : wordDist S X X' + wordDist S Y Y' ≤ wordDist S Y X' + wordDist S X Y' + 2 * δ)
    (hE2 : wordDist S Y X' + wordDist S X Y' ≤ wordDist S X X' + wordDist S Y Y' + 2 * δ) :
    ∃ p q : G, Hyperbolic.IsBetween S X p X' ∧ Hyperbolic.IsBetween S Y q Y' ∧
      wordDist S p q ≤ 8 * δ + 2 := by
  have t1 := wordDist_triangle hS Y X X'
  have t2 := wordDist_triangle hS X X' Y
  have t3 := wordDist_triangle hS X Y Y'
  have t4 := wordDist_triangle hS X Y' Y
  have cYX := wordDist_comm hS Y X
  have cX'Y := wordDist_comm hS X' Y
  have cY'Y := wordDist_comm hS Y' Y
  obtain ⟨p, hp, hXp⟩ := Hyperbolic.exists_isBetween hS X X'
    (i := (wordDist S X Y + wordDist S X X' - wordDist S Y X') / 2) (by omega)
  obtain ⟨q, hq, hYq⟩ := Hyperbolic.exists_isBetween hS Y Y'
    (i := (wordDist S X Y + wordDist S Y Y' - wordDist S X Y') / 2) (by omega)
  have hp' : wordDist S X p + wordDist S p X' = wordDist S X X' := hp
  have hq' : wordDist S Y q + wordDist S q Y' = wordDist S Y Y' := hq
  refine ⟨p, q, hp, hq, ?_⟩
  have cpX := wordDist_comm hS p X
  have cqY := wordDist_comm hS q Y
  have f1 := fullWord_le_or_le_of_le_max_add (hδ p Y X X')
  have f2 := fullWord_le_or_le_of_le_max_add (hδ q X Y Y')
  have f3 := fullWord_le_or_le_of_le_max_add (hδ p q X Y)
  omega

/-- **The full-word quadrilateral.** If the connector pairing `d(B,A) + d(B',A')` is below the
segment pairing `d(A,A') + d(B,B')`, some point between `A` and `A'` is within `8δ + 2` of some point
between `B'` and `B`. -/
theorem exists_close_of_fullWord {G : Type u} [Group G] {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic S δ)
    (A A' B B' : G)
    (hP : wordDist S B A + wordDist S B' A' < wordDist S A A' + wordDist S B B') :
    ∃ p q : G, Hyperbolic.IsBetween S A p A' ∧ Hyperbolic.IsBetween S B' q B ∧
      wordDist S p q ≤ 8 * δ + 2 := by
  have c1 := wordDist_comm hS A B
  have c2 := wordDist_comm hS A' B'
  have c3 := wordDist_comm hS B' B
  have c4 := wordDist_comm hS A' B
  have f1 := fullWord_le_or_le_of_le_max_add (hδ A A' B B')
  have f2 := fullWord_le_or_le_of_le_max_add (hδ A B' A' B)
  by_cases hI : wordDist S A A' + wordDist S B B' ≤
      wordDist S B A' + wordDist S A B' + 2 * δ
  · obtain ⟨p, q, hp, hq, hpq⟩ := exists_close_between hS hδ A A' B B' hI (by omega)
    exact ⟨p, q, hp, Hyperbolic.IsBetween.symm hS hq, hpq⟩
  · exact exists_close_between hS hδ A A' B' B (by omega) (by omega)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.fullWord_le_or_le_of_le_max_add
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.exists_close_between
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.exists_close_of_fullWord
