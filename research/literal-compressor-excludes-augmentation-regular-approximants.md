---
rg: 2
id: literal-compressor-excludes-augmentation-regular-approximants
kind: claim
title: The literal compressor excludes augmentation irreducibles but not all regular-like finite packets
root: true
artifacts:
  - research/literal-compressor-augmentation-proof.md
distinct_from:
  finite-packet-functoriality-has-positive-regular-profile: that gives a general positive regular solution for homogeneous packet functoriality; this computes an operator-norm gap for one natural irreducible enemy and then constructs nonregular faithful exact extensions for the literal compressor edge.
  degree-zero-leavitt-core-characters-are-dirac-haar-mixtures: that classifies limiting characters on the locally finite core; this shows that one explicit sequence converging to its regular character cannot cross the compressor, while other regular-like finite representations can.
---

**ESTABLISHED.**  Let `t in SL_3(F_2)` be a transvection,
`A_m=t tensor I_(2^m)`, and `N=3*2^m`.  At the next degree-zero flattening,
the literal rank-twelve compressor compares

```text
alpha_m=diag(A_m,A_m,I_(6N)),
beta_m =diag(A_m,I_(7N))                              (LCA1)
```

inside `G_m=SL_(8N)(F_2)`.  Let `pi_m` be the irreducible augmentation
representation of the two-transitive action of `G_m` on its nonzero natural
vectors.  Then:

1. for every fixed nonidentity element `g` of the degree-zero direct limit,
   `chi_(pi_m)(g)/dim(pi_m) -> 0`;
2. for every unitary `U`,

```text
||U pi_m(alpha_m) U^* - pi_m(beta_m)|| = 2.           (LCA2)
```

Thus the literal compressor gives a dimension-independent operator-norm
obstruction to this natural irreducible realization of the regular core
character, even though normalized characters alone do not see it.

This does not exclude the regular profile in general.  For the two literal
embeddings `alpha,beta:SL_N(2)->SL_(8N)(2)`, the kernel of
`Res_alpha-Res_beta` on complex representation rings has rank at least three.
It contains the trivial and regular characters and an integral virtual
character outside their span.  Adding a sufficiently large multiple of the
regular character produces faithful, nonregular genuine representations
whose two restrictions are exactly equivalent; their normalized characters
can be made arbitrarily close to regular.

Consequently a single compressor edge and its restriction-multiplicity data
cannot prove that the regular character is not MF.  A successful argument
must add an authenticated same-carrier holonomy or raw nonmonomial occurrence
which is absent from subgroup-extension data.

DERIVATION
literal-compressor-augmentation-proof
