---
rg: 2
id: one-complete-base-type-simultaneously-realizes-disjoint-gadgets
kind: claim
title: One complete base type simultaneously realizes every disjoint existential gadget it realizes separately
distinct_from:
  common-completion-amalgamates-compatible-bespoke-gadgets: that uses compatible finite-dimensional wires or a pre-existing common Fock assignment; this uses elementary extension and saturation and requires instead one common complete base type.
  bespoke-extension-nemesis-library-defeats-diagonal-schedules: that uses closed extension sets to extract a finite obstruction; this identifies their intersections exactly with simultaneous extension, rather than only using the easy obstruction direction.
  finite-static-nemesis-core-needs-canonical-base-embedding: that explains why a common marked representation need not preserve the canonical base profile; this proves simultaneous realization but does not repair that independent embedding gap.
---

**ESTABLISHED.**  Let `p(x)` be a complete tracial type, and let
`E_i(x,y_i)` be a finite or countable family of finite existential unitary
gadgets.  Assume the auxiliary tuples `y_i` are disjoint and there are no
cross-gadget relators.  If every `E_i` is separately realizable over `p`,
then all the `E_i` are simultaneously realizable over one realization of
`p` in a countably saturated elementary extension.

Write `G_i(x,y_i)>=0` for the sum of the squared normalized-HS residuals of
the finitely many relations in `E_i`.  Separate realizability says

```text
(inf_(y_i) G_i)(p)=0                                      (OCB1)
```

for every `i`.  Fix a realization `a` of `p`.  Given finitely many indices
`i_1,...,i_k` and `epsilon>0`, choose each `y_(i_j)` independently so that

```text
G_(i_j)(a,y_(i_j))<epsilon.                              (OCB2)
```

The choices do not interfere because their variables and relations are
disjoint.  Hence the countable partial type

```text
{ G_i(a,y_i)=0 : i>=1 }                                  (OCB3)
```

is finitely approximately satisfiable.  Countable saturation realizes it
exactly.  The base tuple still has type `p`, since the extension is
elementary.

There is a matricial version.  If `p` is realized in a tracial matrix
ultraproduct and every separate extension is matricial, evaluate `(OCB1)`
in a matrix-ultraproduct realization of `p`.  An ultrapower realizes
`(OCB3)`; the resulting iterated matrix ultraproduct flattens, using the
product ultrafilter, to a tracial ultraproduct of matrices.  Therefore, with
the notation of `bespoke-extension-nemesis-library-defeats-diagonal-schedules`,

```text
p in intersection_i C_i
 iff p has one simultaneous matricial extension through every E_i. (OCB4)
```

The reverse implication is immediate.

This removes one possible quantifier ambiguity in the meta-recursive QCA
argument.  It is not necessary to construct compatible pairwise
amalgamations after a **single complete base type** has been shown to extend
every gadget.  What is not valid is the weaker assertion

```text
for every i, some marked model extends E_i
 => one marked model extends all E_i.                    (OCB5)
```

The models on the left may realize different complete base types.  Thus the
HALT/common-completeness obligation is precisely to supply one marked
complete base type satisfying `(OCB1)` for every enumerated gadget.

Finally, simultaneous realization does not imply that the base group embeds
in the union presentation or that its canonical trace is preserved.  Those
are algebraic/canonical-profile conditions outside the complete-type
amalgamation proved here.
