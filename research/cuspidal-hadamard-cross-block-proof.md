---
rg: 2
id: cuspidal-hadamard-cross-block-proof
kind: route
title: Rotate two disjoint restriction-fibre endpoints through their common multiplicity coordinate
target: exact-cuspidal-hadamard-mixing-has-macroscopic-cross-blocks
requires:
  - congruence-endpoint-orbits-are-restriction-ring-fibers
---

Fix one level and two distinct degree-`d_0` cuspidal irreducibles
`delta_1,delta_2` whose restrictions to the square-free core agree.  After
one unitary alignment write the common restriction as `beta` and put
`X_i=delta_i(x)` for the extending involution.

The two endpoint multiplicity vectors have disjoint support in `Irr(Q_p)`.
Thus their overlap in `(ERF3)` is zero and `mu=1`.  The lower bound `(ERF4)`
from `congruence-endpoint-orbits-are-restriction-ring-fibers` consequently
gives

```text
kappa
 <= inf_{V in beta(B_p)'} ||X_2-V X_1 V^*||_(2,d_0)
 <= ||X_2-X_1||_(2,d_0).                                  (HCB1)
```

The same `kappa` works at every congruence level.  This proves the uniform
separation `(ECH2)` without making a choice of bases beyond the common-core
alignment.

Now take the exact direct-sum endpoint on `H_p (+) H_p` and the scalar
Hadamard rotation on its multiplicity coordinate,

```text
W=2^(-1/2) [ 1   1 ] .
             [ -1  1 ]
```

Because the core is `beta (+) beta`, `W` commutes with every core operator.
Conjugating the whole endpoint representation by `W` therefore leaves the
core literally unchanged and preserves every defining relation exactly.  Its
extending involution is

```text
W diag(X_1,X_2) W^*
 = (1/2) [ X_1+X_2   -X_1+X_2 ] .                         (HCB2)
           [ -X_1+X_2  X_1+X_2 ]
```

Relative to the two displayed copies of the complete core decomposition,
the off-diagonal blocks are both `(X_2-X_1)/2`.  With normalized Frobenius
square on the `2d_0`-dimensional direct sum, their total mass is therefore

```text
(1/(2d_0)) * 2 * (1/4)||X_2-X_1||_F^2
 = (1/4)||X_2-X_1||_(2,d_0)^2
 >= kappa^2/4.                                             (HCB3)
```

Refining either copy into irreducible cyclic-core packets does not alter
this calculation: `W` acts only on the duplicate multiplicity coordinate
and commutes with the full common core algebra.  Hence the positive
cross-packet mass survives while the endpoint defect remains exactly zero,
which is precisely the claimed macroscopic Hadamard-mixing witness.
