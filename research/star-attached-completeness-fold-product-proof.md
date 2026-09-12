---
rg: 2
id: star-attached-completeness-fold-product-proof
kind: route
title: Split the star-attached reverse-product fold into orthogonal p and q matrix corners
target: star-attached-completeness-fold-splits-off-p-corner
requires:
  - reverse-product-whitehead-fold-has-finite-fusion
  - projective-star-profile-has-zero-hecke-source
  - finite-prefix-labelled-windows-remain-projective
---

Root additivity and `p+q=1` give the first two identities in `(SCF2)`.
Since `p,q` are orthogonal idempotents, the direct two-by-two multiplication
from the reverse-product Whitehead fold gives

```text
(C_0D_0C_0)(C_1D_1C_1)=JLJ,                           (1)
```

which proves the third identity.

Use the nine projective labels

```text
q@1,q@2,q@3,q@4,q@5,q@6,e_1@7,e_2@8,e_3@9.           (2)
```

The projective matrix-unit lift identifies the associated literal head with
`G_q=SL_9(F_2)`.  In particular `C_1,D_1` are its two standard roots between
the `q@4` and `q@2` labels.

It remains to check the claimed centralization, including all native arms.
Every projective root incident to coordinate `4` has an outgoing coefficient
`s_1T_u` or an incoming coefficient `S_ut_1`; the same statement holds at
coordinate `2`.  Prefix cancellation gives

```text
p s_1=0,             t_1 p=0.                          (3)
```

Every composable product which can meet `x_42(p)` or `x_24(p)` contains one
of the two zero factors in `(3)` at the incident `q`-labelled endpoint.
Roots sharing only the source or only the target commute, and distant roots
commute.  Thus `(3)` and the non-opposite Steinberg commutator law handle
every non-opposite incidence.  For the two opposite q roots, direct
two-by-two multiplication in the elementary image uses `pq=qp=0` and gives
commutation there as well.  Hence `C_0,D_0` commute with every standard root
of `G_q` after the canonical elementary projection, proving `(SCF3)`.  This
is all the finite-model argument needs; no opposite-root commutation is
asserted inside the ambient Steinberg kernel.

On the `p` projective corner at coordinates `4,2`, the two elementary roots
`C_0,D_0` generate `SL_2(F_2)~=S_3`.  Their elementary image is supported on
the `p` corner, while `G_q` is supported on the orthogonal projective
summands `(2)`.  Hence the two elementary-image factors intersect trivially,
which proves `(SCF4)`.  Composing the Steinberg packet with its elementary
image is enough for the finite representation; no assertion about an
ambient Steinberg kernel is needed.

Let `pi_9` be the natural permutation representation of `G_q` on the
nonzero vectors of `F_2^9`, and let `lambda_p` be the six-dimensional left
regular representation of `G_p`.  The tensor product representation

```text
pi=pi_9 tensor lambda_p                                  (4)
```

keeps both `p` roots and all named `q` roots nontrivial.  The exact ranks in
the projective profile are

```text
rank pi_9(P_z)=128,       rank pi_9(E)=32,
pi_9(F)=0.                                               (5)
```

Tensoring with the six-dimensional regular factor multiplies the first two
ranks by six and leaves the last operator zero.  This is `(SCF5)`.  Since
all prefix and Whitehead words lie in `G_q`, while `(1)` holds in the direct
product, `(4)` is the asserted exact finite model of the entire displayed
attachment.
