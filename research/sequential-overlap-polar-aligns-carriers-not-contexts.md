---
rg: 2
id: sequential-overlap-polar-aligns-carriers-not-contexts
kind: claim
title: Sequential overlap polar-aligns carriers but does not align their context observables
distinct_from:
  finite-product-selected-type-mark-does-not-align-carriers: that shows a positive product need not have a nonzero meet; this extracts a genuine analytic common source by thresholding, then locates the later observable-reduction failure.
  fano-cap-sequential-products-form-an-algebraic-naimark-carrier: that keeps all profiles in one rectangular algebraic dilation; this selects one positive profile inside a finite matrix and polar-corrects all its prefixes.
---

**ESTABLISHED FINITE-MATRIX GEOMETRY, BUT NOT SELECTOR
AUTHENTICATION.**  Let `q_1,...,q_m` be projections in a finite tracial
matrix algebra and put

```text
X=q_m...q_1.                                             (SPA1)
```

Assume

```text
||X||_2^2>=a>0.                                         (SPA2)
```

For

```text
P=1_[a/2,1](X^*X)                                      (SPA3)
```

one has the dimension-independent trace bound

```text
tau(P)>=a/(2-a).                                        (SPA4)
```

For every prefix set

```text
Y_c=q_c...q_1P.                                         (SPA5)
```

Then

```text
Y_c^*Y_c>=(a/2)P.                                       (SPA6)
```

Hence the polar corrections

```text
S_c=Y_c(Y_c^*Y_c)^(-1/2)                               (SPA7)
```

are well-defined partial isometries with

```text
S_c^*S_c=P,
R_c=S_cS_c^*<=q_c.                                     (SPA8)
```

Thus positive sequential overlap really does produce one positive-density
analytic common source and one range inside every selected context carrier.
For the Fano cover, `(FMO3)` supplies a profile with
`a>=(4/7)^m`, so `(SPA4)` remains a fixed positive constant for the fixed
instance.  This is stronger than extracting a nonzero meet, and it is
available in canonical matrix microstates without algebraically naming a
support projection.

## Nonreduction is real but harmless for POVM decoding

The ranges `R_c` need not reduce the local context observables.  This can be
maximal even when the product has perfect singular value one on `P`.

Take an orthogonal decomposition

```text
H=H_0 direct-sum H_1 direct-sum H_2,
dim(H_0)=dim(H_1)>0,                                   (SPA9)
```

put `q_1=P_(H_0)` and `q_2=P_(H_0 direct-sum H_1)`, and let `A` be an
involution which swaps `H_0` and `H_1` and preserves `H_2`.  Then

```text
[A,q_2]=0,
X=q_2q_1=q_1,
P=q_1,                                                 (SPA10)
```

for every threshold below one.  If
`mu=tau(q_1)`, the polar range at the second context is still `R_2=q_1`, but

```text
||(1-R_2) A R_2||_2^2=mu,
||[A,R_2]||_2^2=2mu.                                  (SPA11)
```

The selected carrier `q_2` reduces `A`, yet the analytically extracted
subcarrier has full leakage.  Taking the two spectral projections of `A`
gives the same counterexample for a local PVM.

This does **not** obstruct the game decoder.  By the strengthened
`common-source-partial-isometries-decode-one-game-state`, the compressions
`S_c^*P_(c,a)S_c` and `P(I+-B_x)P/2` are legal POVMs even when the displayed
leakage is maximal.  Thus `(SPA9)--(SPA11)` is only a warning against an
unnecessary PVM rounding step, not a selector-authentication firewall.

The remaining canonical-matrix gate is only the raw polar covariance
estimate

```text
sum_(c,x) ||A_(c,x)Y_c-Y_cB_x||_2^2
 <= C times (ordinary actuator-word energy)+o(1),       (SPA12)
```

where `Y_c=q_c...q_1P`.  By
`polar-correction-preserves-povm-covariance`, `(SPA12)` implies

```text
sum_(c,x)||A_(c,x)S_c-S_cB_x||_2^2
 <=C_a times (ordinary actuator-word energy)+o(1),      (SPA13)
```

with `C_a` depending only on the fixed overlap floor `a`.  Positive
sequential mass therefore solves the common-source geometry completely.
Only word payment of the raw prefix covariance remains.

The most direct typed-chain payment is now ruled out sharply.
`full-support-factor-refutes-exact-exhaustive-typed-cap-chain` observes that
the normalized Fano factors `q_(c,lambda)/2` have an exact Parseval product
identity and that typed intertwining errors telescope with a fixed constant.
However, making those typed rows exact in the full-support witness would
produce the forbidden common covariant cap carriers above.  Incidence-local
rows do not telescope through contexts which omit the transported variable;
adding the missing nonincidence rows destroys exact completeness already for
two Pauli contexts.  Thus `(SPA12)` cannot come from a
representation-universal exact cap-product chain.  Its payment must be
finite-matrix/canonical-type-only, or the exact witness must change.

That payment cannot be installed as an exact common-source covariance
identity in the supplied full-support factor model.  If ordinary relations
made the common source nonzero, put every polar range inside its selected cap,
and imposed all rows in `(SPA13)` exactly, then
`full-support-factor-forbids-cap-ranged-common-source-covariance` would force
an excluded honest atom to have trace zero.  Thus the remaining estimate must
use a genuinely finite-matrix/canonical-type mechanism, or a different exact
trace; the strengthened POVM decoder does not make universal exact covariance
compatible with full-support completeness.
