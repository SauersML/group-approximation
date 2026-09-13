---
rg: 2
id: bk-no-compact-open-ideals-are-qd-invisible
kind: claim
title: An extension of a separable nuclear quasidiagonal algebra by an exact ideal with no compact open primitive subset is quasidiagonal
distinct_from:
  brown-dadarlat-ext-trivial-class-gives-qd-extension: that contains Brown-Dadarlat Proposition 4.2 for suspension ideals SI; this allows every exact ideal whose primitive ideal space has no nonempty compact open subset, including cones, fields over noncompact connected spaces and non-Hausdorff spectra such as Rørdam's A_[0,1].
  blackadar-kirchberg-for-uct-quotient-extensions: that is the open extension conjecture for arbitrary quasidiagonal ideals with UCT quotients; this settles ideals with no compact piece in their spectrum, with no UCT and no stable finiteness hypothesis.
  moutzouris-qd-extensions-y-class: that treats ideals locally approximated by ASH algebras and minimal crossed products after tensoring with Q, with UCT quotients, through classification; this uses no classification and no UCT.
  gabe-no-compact-open-prim-embeds-in-cone: that is the embedding theorem and Corollary D for one algebra; this is the consequence for extensions.
artifacts:
  - research/artifacts/bk-spectral-extension-permanence-2026-09-12.md
---

**ESTABLISHED (Theorem 1 of the artifact; lane proof, not yet externally
reviewed).**  Let `0 -> I -> E -> B -> 0` be exact with `E` separable, `I` exact,
and `B` nuclear and quasidiagonal.  If `Prim(I)` has no nonempty compact open
subset, then `E` is quasidiagonal, hence stably finite.

Write `N(E)` for the set of ideals of `E` whose primitive spectrum has no
nonempty compact open subset.  `N(E)` is closed under smaller ideals, extensions
and increasing unions, so it has maximal elements (artifact Lemma 1).

Consequences for STW Problem VII:

1. Problem VII holds for every separable nuclear stably finite `E` with an ideal
   `J ∈ N(E)` such that `E/J` is quasidiagonal.  There is no UCT or trace
   hypothesis.
2. If `E` is separable, nuclear and not quasidiagonal, then `E/J` is not
   quasidiagonal for any `J ∈ N(E)`.  For `J` maximal, every nonzero ideal of
   `E/J` contains a nonzero compact ideal.  `E/J` need not be stably finite, so
   this is a normal form for non-quasidiagonality, not for counterexamples.
3. **Gluing reduction.**  Problem VII is equivalent to its case
   `A = J_1 + J_2` with `J_1, J_2 ∈ N(A)`.  A counterexample `B` gives
   `A = C([0,1], B) = C_0([0,2/3), B) + C_0((1/3,1], B)`, and both ideals are
   AF-embeddable.  Quasidiagonality on an open cover of the primitive spectrum
   carries no information beyond Problem VII; the difficulty is entirely in
   gluing.
4. **Index obstructions need compact support.**  An extension whose ideal is
   compact-free is never a counterexample, even with a nonzero index map.  For
   example, `0 -> C_0(R^2) ⊗ K -> E -> C(T) -> 0` with index `1 ∈ Z`, which lies
   outside Brown--Dadarlat Theorem 3.4.  So suspension-like and cone-like ideals
   cannot carry the K-theoretic index obstruction a counterexample needs.
