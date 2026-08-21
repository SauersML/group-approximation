---
rg: 2
id: one-shared-root-does-not-align-heisenberg-packets
kind: claim
title: One literal shared root does not align two exact regular Heisenberg packets
distinct_from:
  heisenberg-chamber-clocks-escape-until-root-gluing: that duplicates a geometric root as different group elements in different chamber factors; this identifies the repeated root as one literal matrix operator and still produces transverse exact packet reservoirs.
  steinberg-root-shear-plancherel-covariance: that recovers one finite root packet and its spectral PVM from canonical trace; this shows that even exact regular trace and equality of the entire shared-root PVM do not synchronize a second packet.
  tensor-independent-child-carrier-gap: that gives a trace-geometric obstruction once the same carrier is recovered from two transverse algebras; this constructs the transverse algebras and identifies the extra full-overlap scalar needed to put a second generator in the first algebra.
---

Let `H_p` be the order-`p^3` finite Heisenberg group, for an odd prime `p`,
with generators

```text
H_p=<x,y,z : x^p=y^p=z^p=1, z central, [x,y]=z>.        (OSR1)
```

Let `lambda` be its left regular representation on `E=l^2(H_p)`.  Every
nonidentity order-`p` element acts as `p^2` disjoint `p`-cycles.  Consequently

```text
lambda(x) and lambda(z)
```

have exactly the same eigenvalues with exactly the same multiplicities.  Fix
a unitary `S` such that

```text
S lambda(x) S^* = lambda(z).                             (OSR2)
```

Define two exact representations on the same Hilbert space:

```text
rho_1=lambda,
rho_2(g)=S lambda(g) S^*.                                (OSR3)
```

Then

```text
rho_1(z)=rho_2(x)                                        (OSR4)
```

as one literal matrix.  Both packets have the exact regular character, so
all nonidentity packet words have trace zero.  In particular every spectral
projection and every scalar moment of the shared raw root agrees exactly.

Nevertheless their packet algebras

```text
A_1=C^*(rho_1(H_p)),       A_2=C^*(rho_2(H_p))           (OSR5)
```

cannot be equal.  The common operator in `(OSR4)` is central in `A_1`, since
it is `rho_1(z)`, but is noncentral in `A_2`, since it is `rho_2(x)` and

```text
[rho_2(x),rho_2(y)]=rho_2(z) != 1.
```

Equality `A_1=A_2` would make the same matrix both central and noncentral in
one algebra, a contradiction.

Thus Gowers--Hatami exactification of the two finite packets, literal equality
of the repeated root word, exact regular trace, and even equality of the
complete shared-root PVM do **not** produce a common reservoir.

## Four-atom multiplicity rotation

The obstruction persists on the exact positive carrier needed by `G_cc`.
Let `K=C^2 tensor C^2`, let `p_0` and `q_0` be the half projections given by
the first and second bit, and let `T` swap the bits.  Then

```text
T p_0 T^*=q_0,
[p_0,q_0]=0,
tr(p_0)=tr(q_0)=1/2,
tr(p_0q_0)=1/4.                                         (OSR6)
```

On `E tensor K`, put

```text
P=1_E tensor p_0,
Q=1_E tensor q_0,
V=S tensor T.                                           (OSR7)
```

Then `V P V^*=Q`, `V(A_1 tensor 1)V^*=A_2 tensor 1`, and the shared-root
identity `(OSR4)` remains literal after tensoring.  Both rounded packets are
exact and regular, yet the four atoms remain perfectly independent.

This is the smallest multiplicity-rotation countermodel to synchronization
from one raw root word.

## The scalar actually needed

Let `E_1` be the trace-preserving conditional expectation onto `A_1` (after
the fixed finite packet has been exactified), and take the second packet's
noncommuting partner

```text
Y_2=rho_2(y).
```

For a unitary `Y_2`, the scalar

```text
Delta_mix = 1-||E_1(Y_2)||_2^2
          = dist_2(Y_2,A_1)^2                           (OSR8)
```

is zero exactly when `Y_2` lies in the first packet algebra.  If
`Delta_mix=0`, then the shared `rho_2(x)=rho_1(z)` and `Y_2` put the whole
second Heisenberg algebra inside `A_1`; the two faithful regular packet
algebras have the same finite vector-space dimension, so

```text
A_2=A_1.                                                (OSR9)
```

Equivalently, it suffices to share a **second noncommuting raw root word**:
closeness of `Y_2` to its occurrence in the first packet controls
`Delta_mix`.  A cross-Gram statistic involving only functions of the first
shared root cannot control `(OSR8)`, because the countermodel makes all such
statistics exact while `A_1!=A_2`.

Therefore the minimal normalized-HS gluing target is not one-root PVM
agreement.  It is a mixed full-overlap estimate of the form

```text
dist_2(Y_2,A_1)^2
 <= C (presentation defect + trace separation defect),  (OSR10)
```

on a positive four-atom carrier, for one root `Y_2` not commuting with the
literal shared root.  Once `(OSR10)` tends to zero, fixed-finite-group
stability and `(OSR9)` give a common reservoir, after which the rank-two Weyl
triangle kills the diagonal gauge.

The exact countermodel proves that any proposed estimate omitting this mixed
noncommuting generator is false, regardless of how accurately it matches the
shared root's spectral data.
