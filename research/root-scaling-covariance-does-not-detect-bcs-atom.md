---
rg: 2
id: root-scaling-covariance-does-not-detect-bcs-atom
kind: claim
title: Root-scaling covariance alone cannot detect a BCS assignment atom
distinct_from:
  bcs-atom-detects-its-e5-central-root: that asks for a positive payload-to-root overlap in the full wordized microstate; this gives an exact local countermodel to the tempting proof from coefficient eigenvalue relations alone.
  three-line-first-hit-has-invariant-spectator-escape: that charges both source and destination root characters while avoiding the oriented fiber; this kills the central root completely while retaining the desired BCS eigenspace.
  e5-idempotent-root-has-two-pair-extraspecial-cell: that uniformizes spectator characters on a nontrivial central-root sector; this shows why that theorem cannot manufacture the sector.
---

**ESTABLISHED LOCAL FIREWALL.**  Fix an odd prime `p`, commuting
involutions `U_1,...,U_k`, an order-`p` root `Z`, and signs
`epsilon_j in {+1,-1}`.  Impose the coefficient-eigenvalue covariance rows

```text
U_j Z U_j^(-1)=Z^(epsilon_j).                          (RSC1)
```

These are exactly the group consequences one obtains from relations
`u_j a=epsilon_j a` for an idempotent coefficient `a` and a diagonal
Steinberg unit representing `u_j`.

For any desired joint sign `lambda in {+1,-1}^k`, the relations `(RSC1)`
have the one-dimensional exact representation

```text
Z=1,                  U_j=lambda_j.                    (RSC2)
```

Hence the joint assignment projection

```text
P_lambda=product_j (1+lambda_j U_j)/2                 (RSC3)
```

is the identity while the nontrivial spectral support
`S_Z=1-P_(Z,1)` is zero.  In particular no constants `c>0,C<infinity` can
make

```text
tau(P_lambda S_Z)>=c tau(P_lambda)-C E_rel             (RSC4)
```

follow from the exact covariance rows.

The countermodel survives both auxiliaries used in the current compiler.
An independent central involution may be sent to `-1`, so marking does not
remove `(RSC2)`.  If two Heisenberg pairs with common center `Z` are adjoined,
send all four pair generators to `1`; their commutator relations hold because
`Z=1`.  Thus the E5 two-pair packet gives uniformity only after a nontrivial
root sector has been supplied, exactly as stated in
`e5-idempotent-root-has-two-pair-extraspecial-cell`.

Consequently the unary role-packed decoder cannot be proved merely by
reading the assignment signs as automorphisms of the source root.  A valid
payload-to-root theorem must exclude the root-kernel quotient on the actual
BCS carrier by an additional mixed multiplication/corner relation.

