---
rg: 2
id: deleting-one-gap-row-has-the-wrong-orientation
kind: claim
title: Deleting one finite-game row forces its defect large, not small
distinct_from:
  one-gram-vector-decodes-a-finite-bcs-strategy: that proves the complete Gram-Rayleigh gap for all game rows; this audits the proposed use of that gap after one consistency row has been omitted from the presentation.
  fanizza-heterogeneous-compressed-row: that needs one private-to-shared row defect to vanish on a positive-mass Gram carrier; this proves that the bare finite-game gap points in the opposite direction.
---

Let a finite BCS game have finite-dimensional gap `lambda>0`, and use the
one-Gram energy notation of `one-gram-vector-decodes-a-finite-bcs-strategy`.
Separate one consistency row `e=(c,x)` of weight `mu_e>0`:

```text
E_G=E_keep+(mu_e/4)||A_(c,x)G-GB_x||_2^2,
E_G>=lambda||G||_2^2.                                  (DGR1)
```

If a sequence of finite matrix models has

```text
||G||_2^2>=alpha-o(1),        E_keep=o(1),             (DGR2)
```

then necessarily

```text
||A_(c,x)G-GB_x||_2^2
 >=4 lambda alpha/mu_e-o(1).                           (DGR3)
```

Thus deleting a consistency relator from a gapped/non-CE game does not make
the remaining game relations semantically force that row to zero.  On every
positive-mass Gram carrier on which the retained rows become perfect, the
gap forces the omitted row to stay macroscopically **nonzero**.

If some additional matrix-only theorem nevertheless made the omitted row
`o(1)`, `(DGR1)` would force `||G||_2=o(1)` or rule out the matrix microstate
altogether.  That additional theorem would already be the nonhyperlinearity
compiler; it is not supplied by deletion or by the game gap.

The same calculation applies to an omitted predicate row, with its actual
coefficient in the game energy.  It also survives any finite repetition:
repetition increases `lambda`, strengthening the lower bound rather than
reversing its sign.

