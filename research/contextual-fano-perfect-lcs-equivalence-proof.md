---
rg: 2
id: contextual-fano-perfect-lcs-equivalence-proof
kind: route
title: Translate cap profiles to LCS and ternary LCS rows back to maximal Fano caps
target: contextual-fano-cap-compiler-is-equivalent-to-perfect-lcs
requires:
  - rstar-cap-support-is-one-character-row
  - finite-lcs-product-sign-is-exact-or
  - signed-three-face-rstar-petals-are-exact-cap-deletors
  - rstar-two-retained-coordinates-admit-a-fixed-cap-section
---

## From contextual cap support to LCS

Suppose the output has `m` `R_*` contexts.  A cap-supported perfect model
satisfies, at context `c`, one of the seven nonzero character equations from
`(FCH5)`.  Enumerate all `7^m` profiles.  In a profile retain the odd-parity
row defining the affine hull of `R_*` and add the chosen character row.  Every
solution of these two rows lies in `R_*`, because the character excludes the
unique ghost.

On HALT, the profile of the chosen cap-supported model appears in the menu.
On NONHALT, a perfect matrix-ultraproduct model of any profile would forget to
a perfect model of the original contextual `R_*` instance.  The exact finite
LCS OR combines all profiles without choosing one effectively.  This proves
`2 -> 1`, including arbitrary shared contextual auxiliaries: they are simply
retained as shared LCS variables and rows.

## A pure R-star constant gadget

Work in the standard relational convention allowing a variable to occur more
than once in one atomic scope, exactly as in
`signed-three-face-rstar-petals-are-exact-cap-deletors`.

Choose a center context and a desired point `b_0 in R_*` containing both bit
values, for example `b_0=0001`.  For every other `b in R_*`, attach the signed
three-face petal which is unextendible exactly at `b`.  Implement every signed
literal by the repeated-coordinate complement row

```text
R_*(d,d,x,xbar).
```

The six petals leave exactly `b_0` at the center.  Hence its first three
coordinates are pinned zero and its fourth is pinned one.  In the unique
surviving model every petal row is a singleton.  Each complement row has at
most two atoms, so all these supports are Fano caps.  This supplies shared
bits `c_0,c_1` without adding a predicate outside `R_*`.

## From LCS to contextual cap support

Replace a row `x_1+...+x_r=b` by the standard chain of ternary parity rows
using fresh partial sums.  To retain the LCS commutation convention, for
every pair of variables in the original row add an `R_*` context containing
that pair and two fresh variables.  Every exact target model then makes the
original pair commute.  Conversely, in a perfect LCS model all those pairs
already commute, and
`rstar-two-retained-coordinates-admit-a-fixed-cap-section` extends their
joint PVM through one fixed maximal-cap section.  Thus the auxiliary
commutation contexts are cap-supported in the chosen completeness model.

Encode each ternary row by `(CFC2)` or `(CFC3)`.  With `c_0=0`, `(CFC2)` has
exactly the four assignments

```text
{0} x {x,y,z:x+y+z=1},
```

which form the maximal Fano cap with character `(1,1,1)`.  With `c_1=1`,
`(CFC3)` has exactly

```text
{(x,1,y,z):x+y+z=0},
```

the maximal cap with character `(1,0,0)`.  Products of the partial-sum rows
recover the original parity equation, and the added pair contexts recover
all its commutations.  Exact models therefore decode in both directions.

All transformations are finite and effective.  If finite-dimensional values
of the translated NONHALT instances approached one, an ultraproduct would
give an exact translated model and hence an exact source LCS model.  Thus the
strict finite-dimensional soundness needed in `(CFC1)` is preserved.  This
proves `1 -> 2` and the equivalence.
