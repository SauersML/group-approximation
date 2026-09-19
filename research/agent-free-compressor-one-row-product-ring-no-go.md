---
rg: 2
id: agent-free-compressor-one-row-product-ring-no-go
kind: claim
title: One mixed coefficient row does not reflect to its root spectral carrier
invalidates:
  - agent-free-compressor-one-row-implies-kernel-sector
distinct_from:
  hs-steinberg-root-kernel-is-linear-sofic: That asks for full metric reconstruction of a coefficient quotient; this gives exact finite matrix representations showing why the single-row shortcut cannot replace reconstruction.
  root-scaling-covariance-does-not-detect-bcs-atom: That sends the designated root to the identity; this keeps the payload root at fixed positive spectral density while the kernel diagonal has vanishing near-identity density.
  agent-free-compressor-kernel-multiplicity-firewall: That gives an abstract semidirect tensor model for finite packet covariance; this realizes the same multiplicity escape inside genuine rank-five elementary groups of finite coefficient-ring quotients.
---

**ESTABLISHED FIXED-ROW FIREWALL.**  Let `F` be a nonabelian finitely
generated free group, fix `1!=r in F`, and let `p` be an odd prime.  In the
fixed coefficient ring

```text
R=F_p times F_p[F]
```

put

```text
P=(1,0),                    u_f=(1,f)  (f in F).       (ORP1)
```

Then `P` is a central idempotent and

```text
[P,u_f]=0,                  (u_r-1)P=0.                (ORP2)
```

Nevertheless there is a sequence of exact finite-dimensional unitary
representations of the rank-five Steinberg wordization of these rows for
which the payload root

```text
Z=x_13(P)                                             (ORP3)
```

has constant nontrivial spectral density `1-1/p`, while the diagonal unit

```text
D_r=diag(u_r,u_r^(-1),1,1,1)                         (ORP4)
```

has vanishing near-identity spectral density.  Precisely, in normalized
Hilbert--Schmidt norm, every sequence of projections `e_n` satisfying

```text
||(D_(r,n)-1)e_n||_2 -> 0                             (ORP5)
```

also satisfies

```text
tr(e_n)->0.                                           (ORP6)
```

All Steinberg commutator identities and the root relation wordizing
`(u_r-1)P=0` hold with zero defect in these representations.  Hence no
dimension-independent positive-carrier conclusion of the form

```text
tr(e)>=c tr(1-P_(Z,1))-o(1),
||(D_r-1)e||_2=o(1)                                  (ORP7)
```

can follow from the fixed rows `[P,u_f]=0`, `(u_r-1)P=0` and rank-five root
identities alone.

The issue is representation-wide, not an error estimate: on the natural
coefficient module `(ORP2)` does make `u_r` the identity on `PH`, but the
regular unitary representation of the elementary group is not that module.
The root `x_13(P)` records the first product factor, whereas `D_r` carries an
independent second-factor regular multiplicity.  A successful compiler must
therefore authenticate a module/corner correspondence or add a genuinely
non-retractive relation coupling the diagonal action to the payload spectral
space.  Merely adding all finitely many rows `(r_j-1)P=0` does not provide
that authentication: the same product ring satisfies all of them
simultaneously, while one chosen nontrivial `r_j` can be given unbounded order
in the finite quotients used below.
