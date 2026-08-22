---
rg: 2
id: native-forty-two-shell-has-a-noncommuting-pair
kind: claim
title: The native forty-two-label Hecke shell is not a Boolean lamp algebra
distinct_from:
  native-hecke-edge-rank-integrality-is-bounded: that bounds the size of every commuting clique abstractly; this exhibits two labels in the actual forty-two-point shell that fail to commute maximally in an exact defining-relator model.
  balanced-raw-lamp-orbit-cannot-approximate-shell-pvm: that rules out pointwise proximity by trace capacity; this rules out the proposed joint Fourier decoder before any rank comparison.
  two-equivariant-shell-pvms-have-independent-coordinate-escape: that separates two already decoded shell PVMs; this is an exact obstruction inside the raw graph-product lamp algebra.
---

Let

```text
C=SL_3(Z),                 h=diag(2,1,1/2),
S=C h C/C.
```

The shell `S` has `42` points.  Both `hC` and `h^(-1)C` lie in `S`: a signed
long-Weyl permutation in `C` conjugates `h` to `h^(-1)`.  But these two
vertices are not adjacent in the native orbital graph `Theta_h`.  Indeed,
their relative displacement is `h^(-2)`, whose 2-adic elementary-divisor
profile is `(-2,0,2)`, whereas every element of `C h C` has profile
`(-1,0,1)`.

By `native-sl3-group-is-hecke-graph-wreath-product`, the native group is

```text
(graph_product_(x in A/C) C_2) rtimes A.               (N42A1)
```

Consequently the two shell lamps `c_(hC)` and `c_(h^(-1)C)` generate a copy
of `C_2 * C_2`, not `C_2 times C_2`.  In the canonical left-regular
representation of `(N42A1)`, all native defining relations and all mixed
root relations hold exactly, while

```text
||[c_(hC),c_(h^(-1)C)]_add||_2^2=2,                   (N42A2)
```

where `[x,y]_add=xy-yx`.  For the balanced projections
`P_x=(1-c_x)/2`, this says

```text
||[P_(hC),P_(h^(-1)C)]_add||_2^2=1/8.                 (N42A3)
```

Thus zero available relator defect does not imply even approximate
all-pairs commutation of the forty-two raw lamps.  The formal Fourier
product from `fixed-commuting-lamps-have-robust-fourier-atoms` is not a
projection: already `P_(hC)P_(h^(-1)C)` is not self-adjoint.

There is a second exact obstruction to fixed-shell covariance.  Conjugation
by `h` sends the label `hC` to `h^2C`; the latter has elementary-divisor
profile `(-2,0,2)` relative to `C` and lies outside `S`.  Hence `h` does not
normalize the finite 42-label algebra even if one replaces it by a
commuting quotient.  Denominator covariance transports cylinders from a
window `F` to the enlarged window `hF`; it does not close on this one shell.

The viable corrected targets are therefore strictly stronger than the
available mixed-root package: either prove that a selected positive carrier
kills every missing nonedge commutator, or decode compatible atoms on
overlapping commuting cliques while controlling the growing denominator
windows.  The latter is exactly the global lamp/coset-action gate, not a
finite forty-two-coordinate calculation.

This firewall concerns only the congruence-correctable shell program.  It
does not address `sl3-noncorrectable-lambda-sector-has-no-projective-leak`.
