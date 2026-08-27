---
rg: 2
id: coherent-four-potential-pairings-cannot-be-long-c-sixth
kind: claim
title: Reused coherent vertex potentials cannot be made relative C-prime one-sixth by length padding
distinct_from:
  term-pairing-does-not-bypass-signed-hecke-holonomy: that proves the qualitative cocycle and holonomy obstruction; this gives a quantitative piece-counting obstruction to the proposed long-tag relative-small-cancellation repair.
  relative-c-sixth-protects-sign-double-cosets: that proves a Freiheitssatz once genuinely new contours already satisfy relative C-prime one-sixth; this shows the coherent four-potential contours needed by term pairing do not enter that hypothesis merely by lengthening their vertex tags.
  gsc-does-not-separate-sign-double-cosets: that gives an ordinary-small-cancellation counterexample with colliding double cosets; this proves failure of the small-cancellation hypothesis itself for recurrent coherent potential blocks.
---

Consider a symmetrized family of cyclically reduced term-pairing relators.
Suppose one relator has the coherent edge-pairing form

```text
r = H_1 B_1 H_2 B_2 H_3 B_3 H_4 B_4,                 (CFP1)
```

where each `H_i` is a nonempty reduced occurrence of a vertex-potential word
`h_v` or `h_v^(-1)`, the displayed concatenation has no cancellation, and
the `B_i` are the coefficient/separator words.  This is the form obtained by
moving to one side an equality between two labels

```text
h_a h_b^(-1)  and  h_c h_d^(-1).                       (CFP2)
```

Assume every displayed potential occurrence is **recurrent**: the same
labeled word occurs at a genuinely different position in the symmetrized
relator family.  (An inverse occurrence counts after inverting the other
relator.)  Then every `H_i` is a piece.

Put

```text
L_i=|H_i|,       L=sum_i L_i,       b=sum_i |B_i|,
```

in any additive word metric in which `(CFP1)` is reduced.  If the family
satisfied `C'(1/6)`, the piece inequalities would give

```text
6 L_i < |r|=L+b                    for i=1,2,3,4.
```

Summing them yields

```text
6L < 4(L+b),
```

and hence the sharp necessary bounds

```text
L < 2b,                 |r|=L+b < 3b.                  (CFP3)
```

In the actual free-phase escape the phase group commutes with the finite
packet.  After collecting packet coefficients, a paired monomial equality
has one peripheral packet word.  In the standard relative alphabet which
counts a nonidentity peripheral element as one letter, this gives `b<=1`.
But the four potential blocks are nonempty, so `L>=4`, contradicting
`L<2b`.  Thus the recurrent coherent contour cannot satisfy relative
`C'(1/6)` at all in this normal form.  More generally, in an ordinary metric
with a uniformly bounded coefficient part, `(CFP3)` says that no such
contour can be made long by lengthening the coherent vertex tags.  If
`b<=B`, every recurrent four-potential `C'(1/6)` contour would have length
`<3B`.

The recurrence hypothesis is exactly what appears on the cyclic 2-core of
the signed-Hecke term table.  A genuine context projection uses one vertex
potential `h_i` simultaneously in all incident coefficients
`h_i h_j^(-1)`.  Once cross-marginal term pairings contain two occurrences
of that vertex potential, the entire long word `h_i` is a piece, not a fresh
guard.  Passing to longer random words can reduce accidental overlaps
between *different* potentials, but cannot shorten this forced self-overlap.

There are only three ways outside the conclusion, none of which is the
proposed long-tag repair:

1. leave a potential occurrence unrepeated, which removes it from the cycle
   core and does not close the cyclic marginal table;
2. use occurrence-specific tags, which abandons the vertex-potential
   identities needed for star and idempotence and must restore them with
   further coherence relators; or
3. add long guards which are algebraically neutral.  A common guard freely
   cancels from the reduced equality, while a separately killed guard is a
   common long piece of its pairing relator and its killing relator.

Thus the relative `C'(1/6)` protection theorem remains useful only after a
different construction supplies genuinely long contours with no recurrent
four-potential decomposition.  Coefficientwise pairing of the standard
free-phase projections cannot acquire that protection by making its coherent
phase words long.
