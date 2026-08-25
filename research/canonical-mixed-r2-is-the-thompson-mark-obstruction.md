---
rg: 2
id: canonical-mixed-r2-is-the-thompson-mark-obstruction
kind: claim
title: The canonical mixed R2 residual is the marked Thompson defect
invalidates:
  - fixed-group-gh-coercivity-authenticates-canonical-mixed-r2
distinct_from:
  mixed-r2-boundary-is-one-finite-mark-centralizer-commutator: that computes the mixed boundary and its area obstruction after the endpoint gauges have separated; this identifies the fixed normalized boundary with the Thompson mark and gives a dimension-free HS equivalence.
  mixed-r2-cell-couples-shared-s5-extension-multiplicities: that gives the abstract two-chart cancellation once a mixed cell is known; this identifies the actual Bleak--Quick word whose defect that cell would estimate.
  thompson-v-carmichael-compiler-is-linear-mark-collapse: that audits the full unbounded Carmichael compiler; this is the fixed adjacent depth-three seam and already shows that its desired analytic estimate is the marked collapse itself.
---

Use the depth-three labels

```text
p=000,       q=001,       i=010,       j=011
```

and the actual Bleak--Quick words representing

```text
s_i=(i p),             t_j=(j q),             r=(p q).
```

With the convention `x^y=y^(-1)xy`, put

```text
m=t_j^(-1) s_i t_j r^(-1).                                  (CMO1)
```

There are one fixed word `g` and `epsilon in {1,-1}` such that, in Thompson
`V`,

```text
m = g^(-1) b^epsilon g,       b=(01 10 11).                  (CMO2)
```

Consequently there is a universal integer `A`, depending only on these fixed
words and the Bleak--Quick presentation, such that every unitary tuple `U`
with `delta=Def_R(U)` satisfies

```text
| ||m(U)-I||_2-||b(U)-I||_2 | <= A delta.                   (CMO3)
```

Moreover the canonical mixed R2 matrix residual is exactly

```text
||t_j(U)^* s_i(U) t_j(U)-r(U)||_2=||m(U)-I||_2.             (CMO4)
```

Thus a dimension-free `O(delta)` estimate for the actual canonical mixed
occurrence is not a preliminary finite-chart seam lemma: it is equivalent,
up to a fixed linear change of constant, to the full linear marked-word
collapse `||b(U)-I||_2=O(delta)`.

The same remains true for corrected unitaries `X,Y,R` which are linearly
close to the actual occurrences.  If

```text
||X-s_i(U)||_2+||Y-t_j(U)||_2+||R-r(U)||_2 <= L delta,
```

then

```text
| ||Y^*XY-R||_2-||m(U)-I||_2 | <= 2L delta.                 (CMO5)
```

(The displayed `2L` is a convenient loose bound; the direct telescoping
bound is at most twice the `Y` error plus the `X` and `R` errors.)

Finally, fixed-group Gowers--Hatami repair, exact agreement on the shared
`S_5` face, private R2 cells, and all label-valid R4/R5 cells cannot by
themselves prove `(CMO4)`: the exact multiplicity-rotation gauge makes every
one of those inputs zero while leaving the abstract mixed-cell defect
positive.  A proof of the canonical estimate must therefore use genuinely
global Bleak--Quick relator energy strong enough to collapse the mark itself.
It cannot arise from coercivity of the two repaired finite charts alone.
