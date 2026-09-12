---
rg: 2
id: kervaire-laudenbach-holds-for-hyperlinear
kind: claim
title: The Kervaire--Laudenbach conjecture holds for hyperlinear groups
distinct_from:
  hyperlinear-near-representation-criterion: that is an intrinsic characterization of hyperlinearity; this is a consequence of hyperlinearity usable as a falsification test
  non-hyperlinear-group: that asks for a group that is not hyperlinear; this is the necessary condition any such group must be found to violate, if this route is the one used
---

**Terminology.** Nitsche--Thom, *Universal solvability of group equations*,
J. Group Theory 25 (2022) 1--10, arXiv:1811.07737v2, define: "a
Connes-embeddable group is by definition a group which can be embedded into
a certain metric ultraproduct of unitary groups".  That is hyperlinearity;
the two words are interchangeable below.

**The Kervaire--Laudenbach conjecture**, as they state it: for one equation
in one variable, `w in Z * G`, the conjecture "predicts that `w` can be
solved in a group containing `G` if `epsilon(w) != 0 in Z`", where `epsilon`
is the augmentation killing `G`.

**It is a theorem for hyperlinear groups.**  Their Theorem 1.2, attributed
to Gerstenhaber--Rothaus and Pestov: for `G` Connes-embeddable and
`w_1,...,w_k in F_n * G`, if the presentation complex of
`<x_1,...,x_n | epsilon(w_1),...,epsilon(w_k)>` has trivial second homology,
the system is solvable in a group `H` containing `G`; if `G` is finite, `H`
can be taken finite.  Their following sentence: "This proves the original
Kervaire--Laudenbach Conjecture for Connes-embeddable groups, a large class
of groups which includes all sofic groups, and to which to date no
counterexamples are known."

Their own main result strengthens the hypothesis to a covering condition:

> **Theorem 1.3.** Let `G` be a Connes-embeddable group and let
> `w_1,...,w_k in F_n * G`.  If the presentation complex of
> `<x_1,...,x_n | epsilon(w_1),...,epsilon(w_k)>` admits a covering with
> trivial second homology, then the system of equations `w_1,...,w_k` is
> solvable in a group containing `G`.

They note this "proves the first part of Conjecture 1.1 for
Connes-embeddable groups" — Conjecture 1.1 being the *generalized*
Kervaire--Laudenbach conjecture of Klyachko--Thom — and record (their
item (2) in Section 2) that when `G` is Connes-embeddable the system can be
solved inside a Connes-embeddable overgroup.

## Citation correction

The OpenAI nonsofic chapter (see `openai-leavitt-unit-nonsofic`) writes that
Kervaire--Laudenbach "holds for every hyperlinear group [NT22, Theorem 1.3]".
Theorem 1.3 does imply it, being strictly more general, but the *original*
Kervaire--Laudenbach conjecture for hyperlinear groups is their **Theorem
1.2**, credited there to **Gerstenhaber--Rothaus and Pestov**.  Cite Theorem
1.2 (and Gerstenhaber--Rothaus/Pestov) for the plain statement, and Theorem
1.3 only when the generalized or multi-equation form is wanted.
