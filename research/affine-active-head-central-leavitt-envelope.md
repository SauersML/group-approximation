---
rg: 2
id: affine-active-head-central-leavitt-envelope
kind: claim
title: The affine active head embeds faithfully in a coefficient-central binary Leavitt envelope
distinct_from:
  affine-active-corner-has-faithful-binary-leavitt-envelope: that freely adjoins the relative Leavitt family; this additionally makes the four branch operators commute with the entire finite affine coefficient head.
  affine-sign-twist-swaps-active-blocks-but-is-stationary: that realizes only the order-two permutation of the two active Wedderburn blocks; this retains both blocks coefficientwise while adjoining a genuine one-to-two branch.
---

Let `S=k[C_aff]` and let `A in Z(S)` be the affine three-atom active
idempotent. Define

```text
L_A^c(S)=S<s_0,s_1,t_0,t_1>/(
  As_i=s_i=s_iA,          At_i=t_i=t_iA,
  [s_i,a]=[t_i,a]=0       for a in S,
  t_i s_j=delta_(ij)A,
  s_0t_0+s_1t_1=A).                                  (ACL1)
```

It is enough to impose the commutation relations on one fixed `k`-basis of
the finite-dimensional algebra `S`. Then:

1. `S->L_A^c(S)` is injective, so `A!=0`;
2. `L_A^c(S)` is finitely presented over the finite field `k`;
3. the active right module is literally isomorphic to two copies of itself;
4. every unital homomorphism to a finite-dimensional `k`-algebra, or to a
   stably finite ring, kills `A`.

For faithfulness, take countably many copies of the left regular `S`-module.
Split its active summand `AV` into the even and odd copy submodules
`W_0 direct_sum W_1`. The copy-renumbering isomorphisms `AV->W_i` and their
partial inverses are `S`-linear, hence commute with the represented
coefficient algebra, and satisfy `(ACL1)`. The original regular action of
`S` remains faithful.

The finite and stably finite conclusions are the same rectangular-module
argument as in `affine-active-corner-has-faithful-binary-leavitt-envelope`.
The extra centrality is therefore available at no completeness cost. It
makes the active branch coefficientwise visible, rather than only visible as
an abstract projective-module equivalence.
