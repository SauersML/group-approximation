---
rg: 2
id: hyperlinear-computable-hs-dehn-modulus-solvable-word-problem
kind: claim
title: A hyperlinear finitely presented group with computable HS length control has solvable word problem
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  hyperlinear-hs-stable-is-residually-finite: that assumes strict HS-stability and concludes residual finiteness; this assumes only a computable defect bound for trivial words, says nothing about nontrivial words or proximity to exact representations, and concludes decidability of the word problem.
  kleene-self-destroying-microstate-lemma: that needs a machine-indexed compiler and the recursion theorem; this is a statement about one fixed group with no machine inside it, and it replaces the self-referential matrix search by the undecidability of the word problem.
---

Let `G=<S|R>` be finitely presented and hyperlinear, and suppose `G` has
computable HS length control in the sense of
`hs-dehn-modulus-bounded-by-dehn-function`: a computable
`Phi(l,t)` with `Phi(l,t)->0` as `t->0^+` and

```text
w=_G 1,  Def_R(U)<=t   =>   ||w(U)-I||_2<=Phi(|w|,t)           (WP1)
```

for every finite-dimensional unitary tuple `U`.  Then the word problem of
`G` is solvable.

**Corollary.**  A finitely presented group with unsolvable word problem and
computable HS length control is not hyperlinear; explicitly, some nontrivial
word admits no finite-dimensional tuples of relator defect tending to zero
along which it stays bounded away from the identity.

**Corollary.**  For finitely presented hyperlinear groups, computable HS
length control is equivalent to solvability of the word problem (the
converse is the area bound `(HSD1)`).

*Proof sketch.*  Run two semi-procedures on the input word `w`.  The first
enumerates consequences of `R` and halts when `w` appears.  The second
enumerates dimensions, rational skew-Hermitian tuples `K`, and rationals
`t`, forms the Cayley unitaries `U=(I-K)(I+K)^(-1)` (entries in `Q(i)`, dense
in `U(d)^m`), and halts when the exactly computable rational inequalities
`Def_R(U)<=t` and `||w(U)-I||_2^2>Phi(|w|,t)^2` hold.  If `w` is trivial the
second never halts by `(WP1)`.  If `w` is nontrivial, hyperlinearity gives
tuples with defect below any `t` and `||w(U)-I||_2` bounded below by a
constant independent of `t`; choosing `t` with `Phi(|w|,t)` below that
constant, openness of the strict inequalities and density of rational
Cayley tuples make the second procedure halt.  Section 2 of the artifact
has the full argument, including the reduction from the separation form
of hyperlinearity to generator tuples.

The theorem relocates the content of the self-referential route: the
halting-side soundness `(HPB2)` of `hs-pcp-boone-compiler` is a
length-control estimate for one family of bounded-length words with
unbounded area, and the recursion-theorem machine only semi-decides
nontriviality, which undecidability of a fixed word problem already does.
The route `non-hyperlinear-from-computable-hs-dehn-modulus` consumes it.
