---
rg: 2
id: countable-mf-groups-are-epireflective
kind: claim
title: Countable MF groups form an epireflective subcategory of countable groups
artifacts:
  - research/countable-mf-groups-are-epireflective-proof.md
---

Let `Grp_omega` be the category of countable groups and let `MF_omega` be its
full subcategory of operator-MF groups.  The assignment

```text
R_MF(G)=G/Rad_MF(G)
```

extends functorially to a left adjoint

```text
R_MF : Grp_omega -> MF_omega
```

to the inclusion `MF_omega -> Grp_omega`.  Its unit is the surjective radical
quotient, so this is an epireflection.  Explicitly, for every countable MF
group `M`, composition with the quotient gives a natural bijection

```text
Hom_MF(R_MF(G),M) ~= Hom_Grp(G,M).
```

The reflector is idempotent, and a homomorphism `f:G->H` induces the unique
map

```text
R_MF(f):R_MF(G)->R_MF(H),
[g] |-> [f(g)].
```

Thus the MF radical is not merely an intersection of kernels: it is the
kernel of the unit of an idempotent quotient monad.
