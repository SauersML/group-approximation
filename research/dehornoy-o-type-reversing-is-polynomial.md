---
rg: 2
id: dehornoy-o-type-reversing-is-polynomial
kind: claim
title: "Dehornoy's Question 10.11: if a finite triangular presentation defines a monoid of O-type, subword reversing has polynomial complexity; a yes puts every such group's word problem and order in P, and a super-polynomial positive distortion would give a no"
distinct_from:
  isolated-order-word-problems-are-bounded-by-positive-distortion: that bounds word problems of all groups with finitely generated positive cones by D_P and the Dehn function; this is Dehornoy's printed question for the triangular subclass, where the algorithm is subword reversing.
  finitely-generated-positive-cones-are-discrete: that proves structure (a discrete order, a least element with no Baumslag–Solitar self-conjugacy) which any negative answer must get around.
---

**OPEN.** This is Dehornoy's printed question. P. Dehornoy, "Monoids of O-type, subword reversing, and ordered
groups", arXiv:1204.3211, Question 10.11, read 2026-09-19:

> "If a triangular presentation defines a monoid of O-type, does the associated reversing necessarily have a
> polynomial (quadratic?) complexity?"

**Literature check.** A search on 2026-09-19 found no answer. H. L. Su's thesis (arXiv:2512.07035) and his paper
on finitely generated positive cones in `F_n × Z` (arXiv:2608.31103) study positive cones and their languages;
their abstracts do not address it.

**Dehornoy's own evidence.**
- *Examples after the question.* Example 10.3 is cubic, and row 2 of his Table 3 is linear.
- *Example 10.10.* The exponential example `(a, b ; a = bab^{r+1})` is not of O-type.
  `finitely-generated-positive-cones-are-discrete`, item 3, proves why: its least letter would satisfy a
  Baumslag–Solitar relation.

## Setting

`(S ; R)` is a finite presentation that is both right- and left-triangular (Dehornoy, Definition 2.4). Its monoid
`M = ⟨S | R⟩⁺` is of O-type, and `G = ⟨S | R⟩`.
- `G` is finitely presented, and `M − {1}` is the positive cone of an isolated left order (Dehornoy, Corollary 2.7).
- So `G ∈ 𝒞` by `finitely-generated-positive-cones-give-rigid-seeds`.
- Right-triangular presentations are complete for right reversing (Dehornoy, Proposition 4.4).
- Reversing is deterministic, because there is at most one relation `s… = s′…` for each pair of letters.
- `L` is the largest length of a relation side in the finite completion `R̂`.

## The bridge to CAP (lane proof, bh-emitter-a, 2026-09-19; elementary given Dehornoy's lemmas; not reviewed)

1. **Lower bound.** Let `u`, `v` be positive words with `|u| + |v| = n`.
   - Reversing `u^{-1}v` terminates (Dehornoy, §4, since common multiples exist). By his Lemma 3.6 it ends in a
     positive word or the inverse of one, and that word represents `u^{-1}v`.
   - Each step replaces two letters by at most `L`.
   - So the number of steps is at least `(ℓ_+(u^{-1}v) − n)/(L − 2)`, where `ℓ_+` is the shortest positive length.
   - **Consequence.** If `max{ℓ_+(u^{-1}v) : |u| + |v| ≤ n}` is super-polynomial, the answer to Question 10.11 is
     **no**. For example, this happens if some `e^N` with `N` super-polynomial in `n` is a fraction `u^{-1}v` with
     `|u| + |v| ≤ n` (item 5 of `finitely-generated-positive-cones-are-discrete`).
2. **Upper bound.** Suppose right and left reversing of every signed word of length `n` take at most `T(n)`
   steps.
   - This is the general reading of the question. Termination itself holds by completeness and the existence of
     common multiples (Dehornoy, §4).
   - Then `w` reverses to `v u^{-1}` with `|u| + |v| ≤ n + L·T(n)`. Also `w = 1` iff `u^{-1}v` reverses to the empty
     word (completeness). The sign of `w = v u^{-1}` comes from left reversing `v u^{-1}`, the mirror of Lemma 3.6
     for the left-triangular side.
   - So `WP(G)` and the order are in `DTIME(poly(T(n + L·T(n))))`.
   - **Consequence.** A **yes** with polynomial `T` puts the word problem and the order of every such group in P.
3. **For CAP.**
   - A **yes** proves CAP, with the class P, on the finite-triangular part of the finitely generated cone class.
   - A **no** is necessary for a CAP counterexample there.
   - By `finitely-generated-positive-cones-are-discrete`, such a counterexample cannot come from a
     Baumslag–Solitar self-conjugacy of the least positive element, nor from a quasi-central element that
     duplicates it.

## Lesson for general BH

The rigid-seed CAP question, restricted to isolated orders, is a question already in print: Dehornoy's
reversing-complexity Question 10.11.
- **What a counterexample needs.** It must make positive words super-polynomially longer than signed ones.
- **What cannot do it.** The one mechanism Dehornoy found, Baumslag–Solitar duplication, provably cannot occur at
  the bottom of the order.
