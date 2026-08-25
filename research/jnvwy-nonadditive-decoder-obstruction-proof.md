---
rg: 2
id: jnvwy-nonadditive-decoder-obstruction-proof
kind: route
title: Separate exact proof extraction from the nonlinear Boolean-cube decoder
target: jnvwy-exact-proof-atom-decoder-is-not-affine
requires: []
---

Use the exact line--point equations to place every `POINT_6` PVM in each
incident line algebra.  Diagonal lines join every pair of points, so the point
PVMs commute globally; axis lines then make each positive joint table an
individual-low-degree polynomial tuple.  This establishes exact proof-table
extraction without invoking the nonzero-error robust theorem.

Now read the decoder in the low-degree encoding section literally: a
non-Boolean evaluation is replaced by zero.  Over `F_(2^k)`, choose
`theta` outside `{0,1}`.  The three legal multilinear polynomials
`theta ind_y`, `(theta+1) ind_y`, and `0` all decode to the zero word, while
their odd sum is `ind_y` and decodes to the nonzero word `e_y`.

The formula and zero-on-subcube tests force only that every selected clause
has one literal-valued polynomial entry.  They do not impose Booleanity on all
five entries.  Hence PCP soundness is atomwise and cannot identify the decode
of a sum proof with the xor of the component decodes.  Record this as an exact
obstruction to the proposed support-projection proof, without asserting the
existence of a full affine-safe output strategy.
