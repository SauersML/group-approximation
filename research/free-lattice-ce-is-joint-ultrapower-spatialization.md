---
rg: 2
id: free-lattice-ce-is-joint-ultrapower-spatialization
kind: claim
title: The rank-one homogeneous quotient is embeddable exactly when all free-lattice returns spatialize in one ultrapower copy of the base
distinct_from:
  iwahori-index-data-does-not-block-ultraproduct-gluing: that isolates stable compatibility of the two induced edge embeddings in the amalgamated-free-product presentation; this gives an equivalent crossed-product criterion on one finite corner of the amplified translation algebra.
  noncompact-right-holonomy-is-not-compact-profinite: that proves compact right translations have the wrong outer classes inside the translation factor; this allows arbitrary implementers in an ambient matrix ultrapower and identifies exactly what they must do.
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open embeddability assertion; this is a proved if-and-only-if reduction and does not assert either side.
---

**THEOREM (established here; proof in
`free-lattice-joint-spatialization-proof`).**  Let

```text
P=L^infinity(SL_2(Q_2)) rtimes SL_2(Z[1/2])
 =N tensor B(ell^2),
```

and let the torsion-free cocompact free lattice `Lambda'=F_r` act on `P` by
right translations `alpha`.  Choose a finite full projection `q in P` and,
for every free generator `s`, a partial isometry `v_s in P` with

```text
v_s^*v_s=alpha_s(q),       v_sv_s^*=q.                  (FJS1)
```

Put `N_q=qPq` and

```text
beta_s(x)=v_s alpha_s(x)v_s^*,     x in N_q.             (FJS2)
```

The freeness of `F_r` extends the `beta_s` uniquely to an action `beta`.
For the homogeneous-quotient factor `M` in `(DT2)`, the following are
equivalent:

1. `M` is Connes embeddable.
2. `N_q rtimes_beta F_r` is Connes embeddable.
3. There are **one** trace-preserving embedding
   `pi:N_q -> R^omega` and unitaries `U_s in R^omega`, for all free
   generators simultaneously, such that

```text
U_s pi(x) U_s^*=pi(beta_s(x))       (s in S, x in N_q).  (FJS3)
```

Each one-generator version of `(FJS3)` is separately solvable: for every
fixed `s`, amenable crossed-product permanence makes
`N_q rtimes_(beta_s) Z` Connes embeddable, and restricting an embedding gives
some pair `(pi_s,U_s)`.  The open content is therefore not implementation of
any individual return and not local index-three induction.  It is the
intersection problem of realizing all noncompact return automorphisms in one
and the same ultrapower embedding of `N_q`.

This is the action-specific form of the mechanism in Gao, Proposition 5.8,
arXiv:2012.07940.  It also explains why the exact compact-coordinate no-go in
`noncompact-right-holonomy-is-not-compact-profinite` is not yet a matrix
obstruction: `(FJS3)` is allowed to choose a noncanonical embedding `pi` and
non-Cartan implementers `U_s`.

## Combination audit

`separate-return-models-do-not-force-a-common-base` proves that the separately
valid cyclic spatializations cannot be combined formally by pointwise
tensoring, scalar free products, or literal regular-orbit direct sums.
Pointwise tensoring is not linear; scalar free products keep separate copies
of the base; and regular-orbit sums require Folner weights.  Thus a positive
proof still needs structure special to `N_q` and its return automorphisms.

DERIVATION
free-lattice-joint-spatialization-proof
