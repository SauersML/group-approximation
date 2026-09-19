---
rg: 2
id: chromatic-mark-codes-are-metric-agnostic
kind: claim
title: Bounded-area chromatic mark codes kill their mark in every bi-invariant compact model, including normalized Hilbert--Schmidt
distinct_from:
  bounded-area-conjugacy-difference-code-kills-mf-mark: that proves the operator-norm corona conclusion and describes itself as tailored to norm coronas; this shows the identical code kills the mark in every sequence of compact groups with bi-invariant metrics, so in particular in normalized Hilbert--Schmidt and Hamming models.
  infinite-chromatic-commutator-code-kills-mf-mark: that states the norm-corona conclusion and remarks in passing that compact bi-invariant targets also work; this records the Hilbert--Schmidt instance as a theorem and draws the hyperlinearity consequence for every group admitting such a code.
  high-chromatic-sections-force-area-divergence: that is the hyperlinear obstruction for order-three Carmichael sections; this is the analogous obstruction for conjugacy-difference and commutator codes, which have no torsion hypothesis on vertices.
  rf-conjugacy-difference-graphs-finitely-colorable: that obstructs conjugacy-difference graphs in residually finite groups exactly; this obstructs bounded-area codes in every hyperlinear (in particular every sofic) finitely presented group.
artifacts:
  - research/chromatic-mark-codes-metric-agnostic-proof.md
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be finitely presented and let `z` be a
word.  Let `(G_n,d_n)` be compact groups with bi-invariant metrics, for
example

```text
U(k_n) with ||x-y||_op,
U(k_n) with ||x-y||_2 = (tr_(k_n)|x-y|^2)^(1/2)  (normalized trace),
Sym(k_n) with normalized Hamming distance.
```

Let `phi_n:S->G_n` satisfy `delta_n=max_(r in R) d_n(r(phi_n),1)->0`.
Suppose `z` admits either

* a conjugacy-difference code `(CDC1)--(CDC2)` of
  `bounded-area-conjugacy-difference-code-kills-mf-mark`, or
* a commutator code `(CCC1)--(CCC2)` of
  `infinite-chromatic-commutator-code-kills-mf-mark`,

on a graph of infinite chromatic number.  Then

```text
d_n(z(phi_n),1) -> 0.                                   (MA1)
```

Consequently:

```text
Gamma hyperlinear  ==>  z=1 in Gamma.                   (MA2)
```

The same holds for sofic groups (Hamming case, or through hyperlinearity).
Equivalently, in every hyperlinear finitely presented group and for every
nontrivial mark, **every** such code has divergent filling area.

The proofs of the two MF criteria only ever use three properties of the
target: each `G_n` is compact, `d_n` is bi-invariant, and word defect is
bounded by relator area times relator defect.  None is specific to
operator norm.  Therefore the words "operator-norm compactness" in those
nodes describe the setting where they were used, not an ingredient of the
proof.

Consequence for the Leavitt goal.  If
`binary-leavitt-bounded-area-chromatic-code` holds, then
`Delta=St_20(L_(F_2)(1,2))` is not hyperlinear, because its mark
`z=x_13(s_1t_1)` is nontrivial.  This would be the first known
nonhyperlinear group (`non-hyperlinear-group`), and it answers
`binary-leavitt-unit-group-hyperlinear` in the negative for the group
identified with `Delta` in the goal node.  The reduction is
`non-hyperlinear-group-via-binary-leavitt-chromatic-code`.  Route 5 of
`property-t-free-leavitt-full-mf-radical` is therefore at least as hard as
the existence of a nonhyperlinear group.  It is not an MF-specific
(T)-free route.

DERIVATION
chromatic-mark-codes-metric-agnostic-proof
