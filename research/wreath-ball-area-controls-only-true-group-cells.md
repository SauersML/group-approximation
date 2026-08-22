---
rg: 2
id: wreath-ball-area-controls-only-true-group-cells
kind: claim
title: Wreath ball tables are area controlled but moving quotient-kernel cells are not
distinct_from:
  hs-dehn-modulus-bounded-by-dehn-function: that bounds one trivial word by its filling area; this applies it simultaneously to the radius-R wreath multiplication table, proves a diagonal growing-window theorem, and separates genuine group cells from false-in-the-group congruence quotient cells.
  finite-wreath-relative-tangent-moduli-vanish: that contracts approximate cocycles once the full finite multiplication table is small; this computes exactly which part of that table a fixed presentation controls.
  bounded-width-regular-character-compiler: that asks for a quantum-sound bounded-width compilation of finite group-table loss; this shows why simply evaluating quotient representatives cannot supply such a compiler.
---

Fix a finite presentation `G=<S|R>` and, for every element of the word ball
`B_G(R)`, choose a representative `w_g` of length at most `R`.  Let
`T_R` contain every multiplication cell

```text
w_g w_h w_k^(-1),       g,h,k in B_G(R),       gh=k.   (WBT1)
```

Every word in `(WBT1)` is trivial in `G`, has length at most `3R`, and hence
area at most `Dehn_G(3R)`.  Therefore every unitary tuple `U` satisfies

```text
Def_(T_R)(U)
 <= Dehn_G(3R) Def_R(U).                                (WBT2)
```

This applies in particular to all lamp conjugates and mixed wreath products
whose representing words lie in the radius-`R` ball.

The loss is nonuniform in `R`, but it cannot prevent **all** growing table
control.  For every sequence `U_n` with presentation defects `delta_n->0`,
there is a sequence `R_n->infinity` such that

```text
Dehn_G(3R_n) delta_n ->0,
Def_(T_(R_n))(U_n)->0.                                  (WBT3)
```

Choose increasing cut times so that after the `j`-th cut
`delta_n Dehn_G(3j)<=1/j`, and put `R_n=j` between consecutive cuts.
Thus a proposed nonlinear entropy family cannot merely keep escaping every
growing genuine group window: every vanishing-defect sequence has a slowly
growing window on which the whole true multiplication table is accurate.

There is, however, an exact obstruction to importing the finite-group
tangent contraction.  Let `q:G->H` be a finite quotient and choose word
lifts `s_x` of `x in H`.  A quotient multiplication cell

```text
s_x s_y s_(xy)^(-1)                                    (WBT4)
```

lies in `ker q`, but need not be the identity in `G`.  If it is nontrivial,
no van Kampen diagram exists and presentation defect gives **no** upper bound
on its matrix value.  Canonical regular trace in fact asks a fixed nontrivial
kernel word to have trace near zero, not to be close to the identity.  In a
congruence sequence the killed kernel words must therefore move to infinity;
their quotient-table correctness is extra model structure, not a consequence
of the fixed presentation.

Consequently `(WBT2)` plus
`finite-wreath-relative-tangent-moduli-vanish` gives a subquadratic local
cover only for models already known to have small full finite-packet table
defect.  It does not cover all presentation microstates.  Conversely, rapid
growth of `Dehn_G` or of quotient section lengths supplies only a failure of
this correction proof, not a `c d^2` family: `(WBT3)` always leaves a diagonal
accurate true table, and filling area is an upper bound rather than a source
of separated models.

The remaining entropy seam is now exact.  One must either control the moving
quotient-kernel cells by a new regular-character compiler, yielding the
subquadratic finite-packet cover, or construct many non-conjugate
presentation microstates whose moduli survive every diagonal true-ball table
while living in those uncontrolled moving kernel directions.
