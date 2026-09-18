import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalContig
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcSubArc
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual contiguity clauses: list and arc combinatorics

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12b.

Elementary part (a) of the split of `P10ExtremalContig.RoseExtremalContigResidualStatement`
(module `Piece10Live/ExtremalResidual`).

* `movePred_alpha`: the kept-dart predicate `!z d && !z (alpha d)` of a move is invariant under
  `alpha`.
* `filter_invDarts_symm`: for an `alpha`-invariant predicate `p`, filtering the reversed arc is
  reversing the filtered arc.
* `filter_decomposition`: filtering a cycle `s₁ ++ a⁻¹ ++ s₂ ++ b` is
  `s₁.filter p ++ (a.filter p)⁻¹ ++ s₂.filter p ++ b.filter p`.
* `noWrapSubArc`, `noWrapSubArc_darts`: a contiguous piece `mid` of an arc
  `A.darts = pre ++ mid ++ post` is read by the arc with base position `A.start + |pre|` (no
  reduction modulo the cycle length) as long as `A.start + |pre| ≤ |cyc|`.  Unlike
  `P07InnerPocket.CyclicArc.subArcArc`, the base position is literally above `A.start`, which is
  what the positional containment clauses of the residual statement ask for.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual

universe u w v

open Embedded P10Rose.FilterMove

/-- **The kept-dart predicate is `alpha`-invariant.** -/
theorem movePred_alpha (M : CombMap.{v}) (z : M.Dart → Bool) (d : M.Dart) :
    movePred M z (M.alpha d) = movePred M z d := by
  unfold movePred
  rw [M.alpha_involutive d, Bool.and_comm]

section Lists

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Filtering a reversed arc by an `alpha`-invariant predicate.** -/
theorem filter_invDarts_symm (X : DiscDiagram.{u, w, v} W) (p : X.toCombMap.Dart → Bool)
    (hp : ∀ d, p (X.toCombMap.alpha d) = p d) (l : List X.toCombMap.Dart) :
    (invDarts X l).filter p = invDarts X (l.filter p) :=
  calc (invDarts X l).filter p = (l.reverse.map X.toCombMap.alpha).filter p := rfl
    _ = (l.reverse.filter (p ∘ X.toCombMap.alpha)).map X.toCombMap.alpha := List.filter_map
    _ = (l.filter (p ∘ X.toCombMap.alpha)).reverse.map X.toCombMap.alpha := by
      rw [List.filter_reverse]
    _ = (l.filter p).reverse.map X.toCombMap.alpha := by
      rw [List.filter_congr (p := p ∘ X.toCombMap.alpha) (q := p) (fun x _ => hp x)]
    _ = invDarts X (l.filter p) := rfl

/-- **Filtering a four-block cycle.**  If `c = s₁ ++ a⁻¹ ++ s₂ ++ b` and the kept parts of `a`
and `b` are `a'` and `b'`, then the kept part of `c` is `s₁' ++ a'⁻¹ ++ s₂' ++ b'`. -/
theorem filter_decomposition (X : DiscDiagram.{u, w, v} W) (p : X.toCombMap.Dart → Bool)
    (hp : ∀ d, p (X.toCombMap.alpha d) = p d) {c s₁ s₂ a b a' b' : List X.toCombMap.Dart}
    (hc : c = s₁ ++ invDarts X a ++ s₂ ++ b) (h₁ : a.filter p = a') (h₂ : b.filter p = b') :
    c.filter p = s₁.filter p ++ invDarts X a' ++ s₂.filter p ++ b' := by
  rw [hc, List.filter_append, List.filter_append, List.filter_append,
    filter_invDarts_symm X p hp, h₁, h₂]

end Lists

section Arcs

variable {Dart : Type*} {cyc : List Dart}

/-- **The non-wrapping sub-arc** of `A` reading the middle piece of `A.darts = pre ++ mid ++ post`,
with base position `A.start + |pre|`. -/
def noWrapSubArc (A : CyclicArc cyc) (pre mid post : List Dart)
    (h : A.darts = pre ++ mid ++ post) (hnw : A.start.1 + pre.length ≤ cyc.length) :
    CyclicArc cyc where
  start := ⟨A.start.1 + pre.length, by omega⟩
  length := mid.length
  length_le := by
    have h₁ := P07InnerPocket.CyclicArc.length_add_of_darts_eq A h
    have h₂ := A.length_le
    omega

theorem noWrapSubArc_start (A : CyclicArc cyc) (pre mid post : List Dart)
    (h : A.darts = pre ++ mid ++ post) (hnw : A.start.1 + pre.length ≤ cyc.length) :
    (noWrapSubArc A pre mid post h hnw).start.1 = A.start.1 + pre.length :=
  rfl

theorem noWrapSubArc_length (A : CyclicArc cyc) (pre mid post : List Dart)
    (h : A.darts = pre ++ mid ++ post) (hnw : A.start.1 + pre.length ≤ cyc.length) :
    (noWrapSubArc A pre mid post h hnw).length = mid.length :=
  rfl

/-- **The non-wrapping sub-arc reads the middle piece.** -/
theorem noWrapSubArc_darts (A : CyclicArc cyc) (pre mid post : List Dart)
    (h : A.darts = pre ++ mid ++ post) (hnw : A.start.1 + pre.length ≤ cyc.length) :
    (noWrapSubArc A pre mid post h hnw).darts = mid := by
  show (noWrapSubArc A pre mid post h hnw).rotated.take mid.length = mid
  rw [Embedded.CyclicArc.rotated_eq_rotate, noWrapSubArc_start, ← List.rotate_rotate,
    P07InnerPocket.CyclicArc.rotate_start_eq_append A h, List.rotate_append_length_eq,
    List.append_assoc]
  exact List.take_left

end Arcs

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.movePred_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.filter_invDarts_symm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.filter_decomposition
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.noWrapSubArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.noWrapSubArc_start
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.noWrapSubArc_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalResidual.noWrapSubArc_darts
