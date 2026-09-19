---
rg: 2
id: role-packed-forbidden-reflection-is-not-a-group-word
kind: claim
title: The role-packed forbidden reflection cannot be one literal group word
distinct_from:
  involution-hecke-corner-has-no-proper-literal-projections: that classifies projections of the form qgq in one involution corner; this excludes making the aggregate forbidden projection itself the negative spectral projection of a literal word.
  role-packed-bcs-gap-is-one-idempotent: that constructs the aggregate as a finite-support group-algebra projection; this proves that finite support does not make its reflection a group element.
  central-marked-two-cycle-zero-compression-cell: that consumes a source named by two literal grading involutions; this shows why that cell cannot take B_f as one additional literal grading.
---

**ESTABLISHED CANONICAL-TRACE OBSTRUCTION.**  Keep the finite central product
of each context packet with the extraspecial role packet in
`role-packed-bcs-gap-is-one-idempotent` embedded, with common central
involution `J`.  For a forbidden atom in a nonempty `k_i`-variable context,
the product `R_iP_i` is the character idempotent of the finite central
product of the role diagonal subgroup and the context subgroup.  Therefore

```text
tau_G(R_iP_i)=1/(m 2^(k_i+1)).                         (RFW1)
```

The summands are orthogonal, so

```text
0<tau_G(B_f)=m^(-1)sum_i 2^(-(k_i+1))
             <=M/(4m)<=1/4.                           (RFW2)
```

There is no group element `g` in any overgroup preserving these embedded
central-product packets for which

```text
g=1-2B_f                                                (RFW3)
```

in the faithful complex group algebra.  Indeed `(RFW3)` and idempotence of
`B_f` make `g` a selfadjoint involution.  If `g=1`, then `B_f=0`; if `g!=1`,
the canonical group trace gives

```text
tau_G(B_f)=(1-tau_G(g))/2=1/2,                         (RFW4)
```

and both alternatives contradict `(RFW2)`.

Consequently the established two-cycle relation
`central-marked-two-cycle-zero-compression-cell` cannot close
`finite-depth-role-packed-aggregate-escape` by adjoining `1-2B_f` as one
literal grading generator.  A successful cell must either use a genuinely
multi-piece group-ring corner, change the packet embeddings through the
load-bearing relation, or authenticate the aggregate only on the
representation-dependent reached carrier.

DERIVATION
role-packed-forbidden-reflection-word-proof
