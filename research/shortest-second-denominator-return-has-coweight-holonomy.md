---
rg: 2
id: shortest-second-denominator-return-has-coweight-holonomy
kind: claim
title: The shortest second denominator return closes the root type but leaves an amenable coweight holonomy
distinct_from:
  first-root-parahoric-target-has-a-distinct-double-coset-type: That rules out every integral diagonal return and isolates the need for a second denominator; this classifies the six Weyl-conjugate denominator returns and computes the first closed typed loop.
  coxeter-hexagon-admits-flat-affine-corrector: That gives an abstract mod-two affine gauge on all six chambers; this computes the literal dyadic diagonal word left by the shortest native two-return loop.
  three-parahoric-weyl-triangle-has-affine-gauge-countermodel: That constructs a finite substitute affine lamp model; this identifies the actual arithmetic holonomy as `diag(2,2,1/4)` and proves why its ordinary product word has no fixed leakage.
---

# Exactly two shortest returns

Put

```text
h=diag(2,1,1/2),       u=x_12(1),       s=s_23,
z=s^(-1)u^2s=x_13(plusOrMinus 2).                      (SDR1)
```

The first rectangular edge changed the source root type `u` into `z`.
To return `z` to `u` using one signed Weyl coordinate change and one of the
six conjugate denominators, first conjugate by `s`, obtaining `u^2`.  A
denominator `h_w` with coweight

```text
lambda_w in S_3.(1,0,-1)                               (SDR2)
```

then sends `u^2` to `u` exactly when

```text
(lambda_w)_1-(lambda_w)_2=-1.                          (SDR3)
```

There are exactly two such permutations:

```text
h_0=h^(-1)=diag(1/2,1,2),
h_1=s_12 h s_12^(-1)=diag(1,2,1/2).                   (SDR4)
```

Consequently the two shortest typed returns are

```text
T_0=h_0s,                 T_1=h_1s,                    (SDR5)
T_i z T_i^(-1)=u.                                      (SDR6)
```

The first is the literal backtrack.  The second is the unique alternative
among the six native denominator directions for this fixed root-coordinate
change.

# The alternative return misses the carrier by one coweight translation

On the returned `u`-packet the relative loop holonomy is

```text
k=T_1T_0^(-1)=h_1h
 =diag(2,2,1/4).                                       (SDR7)
```

It is nontrivial and centralizes the entire root group `x_12(*)`, since its
first two diagonal entries agree.  On the source `z`-packet the conjugate
holonomy is

```text
T_0^(-1)T_1=s^(-1)ks=diag(2,1/4,2),                   (SDR8)
```

which similarly centralizes `x_13(*)`.  Thus the loop closes the finite
root **type**, but its two returns land on carriers separated by the
coweight translation `(1,1,-2)`.

The ordinary product word `(SDR7)` does not charge this mismatch.  It is a
genuine nonidentity element of the arithmetic diagonal torus, not a
relator.  On the finite-torus hexagonal cut `E_M` from
`affine-weyl-folner-cut-survives-native-parahoric-triangle`, every fixed
coweight translation has

```text
||kE_Mk^(-1)-E_M||_2^2=O(1/M).                         (SDR9)
```

Hence the loop product is separated in canonical trace, but its action on
the conductor cutoff has vanishing boundary energy.  Multiplying the two
return words merely names `k`; no group relation asks that word to equal the
identity.

This gives the exact bounded typed-graph outcome.  A shortest second
denominator return exists, but the nonbacktracking return is not a
same-carrier return.  Its residual holonomy lies entirely in the amenable
coweight algebra already covered by the Folner escape.  A useful loop must
either authenticate the two returned carriers as literally equal, thereby
charging `(SDR9)` elsewhere, or include a transverse raw incidence whose
holonomy leaves the diagonal coweight subgroup.  One extra native
denominator and the root-coordinate change do neither.

