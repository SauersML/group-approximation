---
rg: 2
id: canonical-b7-or3-corner-defeats-finite-prefix-actors
kind: claim
title: A canonical B7 OR3 corner defeats every finite prefix actor
artifacts:
  - experiments/or3_cycle_raw_prefix_covariance.py
distinct_from:
  raw-prefix-covariance-reduces-to-nonincidence-cap-commutators: that constructs the minimal seven-dimensional matrix witness and identifies its sole prefix term; this authenticates the complete witness inside a positive canonical finite-group corner.
  canonical-fano-free-product-defeats-finite-actor-payment: that rules out finite actors for an uncompressed free Fano commutator; this retains the sequential Gram cut and the exact prefix-compressed SPA12 payload allowed by the weaker live target.
---

**ESTABLISHED PREFIX-ACTOR NO-GO.**  Let

```text
K=B_7=C_2^7 semidirect S_7,                            (BPC1)
```

and let `rho` be its natural signed-permutation representation on `C^7`.
The representation is irreducible over `Q`: the diagonal subgroup has seven
distinct coordinate weight spaces, and transitivity of `S_7` forces any
invariant sum of them to be zero or all of `C^7`.  Let `p_rho in Q[K]` be
its primitive central projection.

Every involution in the exact OR3 Berge-triangle model of
`raw-prefix-covariance-reduces-to-nonincidence-cap-commutators` is a signed
permutation matrix.  This includes the three global shared-variable
observables, every local OR3 observable, the three cap reflections
`2q_c-1`, and the source reflection `2P-1`.  Its seven rank-one assignment
atoms are rational elements of the block `p_rho Q[K]`: coordinate atoms are
spectral halves of diagonal signs, while the two rotated atoms are the two
spectral halves of the transposition of coordinates zero and four, cut by
their coordinate plane.

Consequently the entire exact model lifts to the rational canonical corner
`p_rho Q[K]`.  All six incidence rows vanish there.  With

```text
X=q_3q_2q_1,
P=1_[3/28,1](X^*X),                                   (BPC2)
```

the sole raw prefix term is still

```text
D=q_3[B_(x_31),q_2]q_1P.                              (BPC3)
```

For an operator `T` in the `rho` block, canonical regular trace is

```text
tau_K(p_rho T)=7/|K| Tr_7(T).                          (BPC4)
```

Since `|K|=2^7 7!=645120`, the exact values are

```text
tau_K(p_rho X^*X)=1/61440,
tau_K(p_rho P)=1/46080,
||p_rho D||_(2,tau_K)^2=1/92160.                      (BPC5)
```

The artifact checks every signed-permutation assertion and all three
fractions over exact rational arithmetic.

Attach any finite Bass--Serre actor to `K`, or any finite collection of such
actors combined into one finite graph of groups.  The canonical embedding of
the finite base `K` extends exactly through the actor by
`canonical-types-extend-every-finite-bass-serre-actor`.  Hence every actor
relator has zero defect while the rational selected corner, its sequential
source, and the prefix defect `(BPC5)` are unchanged.

Therefore no finite packet, finite-subgroup HNN transporter, or finite
graph-of-groups actor can prove even the prefix-compressed alternative in
`canonical-or3-nonincidence-cap-commutator-payment`.  The remaining actor
must contain a payload-sensitive non-Bass--Serre relation or an infinite
actor whose canonical extension is obstructed; finite type transport is
completely excluded.

