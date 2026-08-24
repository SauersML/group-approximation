---
rg: 2
id: mf-semantic-closure-transplantation
kind: claim
title: Camouflage surgery transplants the entire MF semantic closure operator
distinct_from:
  mf-relation-closure: That theorem defines the closure operator for one ambient group; this computes how the full operator changes under the camouflage quotient.
  full-mf-radical-absorber: That theorem computes only the radical at the trivial relation; this formula applies at every normal subgroup and identifies the complete lattice of MF quotients.
artifacts:
  - research/mf-semantic-closure-transplantation-proof.md
---

For a normal subgroup `N normal G`, define

```text
cl_MF^G(N)=q_N^(-1)(Rad_MF(G/N)).
```

Equivalently, this is the intersection of the kernels of all MF-target maps
from `G` which kill `N`.

For the camouflage epimorphism `pi_Q:C_d(Q)->Q`, every normal subgroup
`N normal C_d(Q)` satisfies

```text
cl_MF^(C_d(Q))(N)
  = pi_Q^(-1)(cl_MF^Q(pi_Q(N))).                    (S1)
```

In particular,

```text
Rad_MF(C_d(Q))=pi_Q^(-1)(Rad_MF(Q)).                (S2)
```

and

```text
C_d(Q)/N is MF
  iff d belongs to N and Q/pi_Q(N) is MF.           (S3)
```

If `Q` is MF, its universal MF reflection is realized by the split quotient
`pi_Q`, and the exact radical is the singly normally generated subgroup
`normalClosure(d)`.

The assignments

```text
P |-> pi_Q^(-1)(P),        N |-> pi_Q(N)
```

are inverse order isomorphisms between the MF-closed normal subgroups of `Q`
and those of `C_d(Q)`.  Equivalently, the complete lattices of MF quotients of
the two groups are canonically identical.
