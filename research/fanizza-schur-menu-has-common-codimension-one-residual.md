---
rg: 2
id: fanizza-schur-menu-has-common-codimension-one-residual
kind: claim
title: The universal arity-four Schur pencil and a reset direction share fixed nondegenerate rank-fifteen hyperplanes
artifacts:
  - experiments/common_schur_residual_hyperplane.py
  - experiments/common-schur-residual-hyperplane.json
distinct_from:
  invertible-direction-schur-rank-compiler: that proves every baseline and every nonzero derivative is full rank; this finds one fixed pair of codimension-one source/target hyperplanes on which all baseline sectors and a chosen reset derivative remain nondegenerate.
  derived-lifted-gauge-reset-spin-bridge: that must package the sectorwise residual congruences into one finite incidence; this closes its finite linear-algebra existence audit but not that group-incidence step.
---

Use the archived arity-four field-multiplication pencil

```text
U(x)=M_(a(x)) in M_16(F_2),
a(x)=a_0+sum_i x_i b_i in F_(2^16).
```

Let `alpha=0x1` and `beta=0x4ddc` in the polynomial basis.  Put

```text
P_0=ker(alpha^T) <= F_2^16,
Q_0=ker(beta^T)  <= F_2^16.                            (CRH1)
```

Then for every one of the sixteen selector values `x`, the cross-pairing

```text
(p,q) |-> p^T U(x) q
```

restricts to a nondegenerate pairing on `P_0 times Q_0`.  The same is true for
the reset multiplier

```text
b_reset=0x2ce6.                                        (CRH2)
```

Thus all sixteen baseline spin forms and this derivative form contain a
rank-fifteen residual on the same source and target hyperplanes.  Their spin
dimension on that residual is `2^15`; one complementary hyperbolic pair
restores the common baseline scale `2^16`.

The exact replay also finds eight other compatible nonzero reset multipliers:

```text
0xb0eb, 0x9c0d, 0x762, 0x2b84, 0xb789,
0xb8aa, 0x24a7, 0x841.                                 (CRH3)
```

More strongly, the first three compatible directions form the complete
nonzero part of a two-dimensional linear subspace:

```text
0x2ce6 xor 0xb0eb = 0x9c0d.                            (CRH4)
```

Consequently one fixed pair of residual hyperplanes works simultaneously
for an entire natural `GL_2(F_2)=S_3` orbit of reset directions.  The replay
enumerates every compatible two-plane, rather than inferring `(CRH4)` from
three separate rank checks.  This is the finite linear-algebra input needed
by an `S_3`-equivariant reset incidence; it does not by itself constrain the
incidence's multiplicity intertwiners.

Not all fifteen nonzero directions work for this fixed hyperplane pair.  That
does not restrict the compiler: a linear change of the four selector
coordinates sends any prescribed nonzero gauge direction to `b_reset`, leaves
the affine value set `a_0+span(b_1,...,b_4)` unchanged, and the final Schur row
still realizes every Boolean truth table.  Hence every gauge-doubled Fanizza
predicate may use the same common residual after reparameterization.

The restricted bilinear forms are nondegenerate but are not asserted equal.
For each of the finitely many selector sectors there is a symplectic
congruence to one standard rank-fifteen form.  Turning those congruences into
one ordinary finite incidence with no unwanted representation types is the
remaining group-theoretic step in `derived-lifted-gauge-reset-spin-bridge`.
