---
rg: 2
id: two-step-fold-loop-has-finite-64-model
kind: claim
title: The shared two-step fold return has a finite marked model of order 64
artifacts:
  - research/two-step-fold-loop-64-proof.md
distinct_from:
  shared-cousin-arm-loop-has-finite-matrix-fusion: that absorbs the range fold in a central scalar-root quotient before any further coefficient multiplication; this propagates the fold through two literally shared commuting arm occurrences and returns a nontrivial mark.
  marked-a3-output-whitehead-has-finite-gl4-model: that specializes one already-multiplied A3 payload before applying an opposite-root Whitehead; this keeps the three separate fold coefficients and applies the same nested word to all three.
---

**ESTABLISHED EXACT TWO-STEP COUNTERMODEL.**  Write the range-fold root
occurrences as

```text
C_0 C_1=J,                                             (TSF1)
```

and use the same two coefficient-arm occurrences `S,T` in all three
two-step returns

```text
D_i=[T,[C_i,S]],             D=[T,[J,S]].              (TSF2)
```

This is the literal group-word form of first composing the fold output with
the shared `s_u` arm and then composing on the left with the shared `t_u`
arm.  Include the distant-root rows

```text
S^2=T^2=1,                   [S,T]=1.                  (TSF3)
```

Thus `(TSF2)` does not duplicate either arm and does not omit their required
commutation.

The exact table

```text
C_0C_1=J,      D_0=M,      D_1=1,      D=M            (TSF4)
```

has a finite model with `M` nonidentity.  Let

```text
B=F_2[e,h]/(e^2,h^2)
```

and let the commuting involutions `T,S` act on the additive group of `B` by
multiplication by `1+e,1+h`, respectively.  In the semidirect product

```text
G=B_additive semidirect <T,S>,                         (TSF5)
```

put

```text
C_0=c(1),       C_1=c(h),       J=c(1+h),
M=c(eh).                                                   (TSF6)
```

Then `G` has order `16*4=64`, `(TSF1)--(TSF4)` hold exactly, and `M!=1`.
Its left regular representation is therefore an exact finite-dimensional
unitary model with

```text
||lambda(M)-1||_op=2.                                  (TSF7)
```

Consequently, merely moving the fold out of the central output root and
sandwiching it between one shared arm pair does not imply `(BAC1)`.  The
scalar-root quotient from the preceding matrix-unit model is gone, but a
finite second-difference model replaces it.  A successful prototype must
also authenticate enough of the individual intermediate root occurrences
to exclude this square-zero affine action; the returned long-root equality
alone is insufficient.

This is a scoped obstruction to the displayed two-step cell, not a finite
model of the entire Leavitt/Whitehead presentation.  No Property `(T)`,
Kazhdan input, stability theorem, trace hypothesis, or literature result is
used.

DERIVATION
two-step-fold-loop-64-proof

