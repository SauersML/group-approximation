---
rg: 2
id: balanced-direct-sums-preserve-rectangular-excess
kind: claim
title: Balanced self-similar direct sums preserve rather than amplify rectangular deficiency density
distinct_from:
  arity-imbalanced-schur-heads-have-a-stationary-exit: that studies unital maps of one fixed semisimple packet and exhibits a regular stationary exit type; this is a representation-free rank and normalized-HS calculation for arbitrarily deep, dimension-activated rectangular pencils.
  fixed-rectangular-kernel-return-factorization-is-impossible: that uses the regular factor to forbid an exact return factorization; this permits a genuinely matrix-only return but proves that balanced recursive copying cannot improve its density or error modulus.
  adaptive-rectangular-kernel-column-extraction: that extracts an original-model carrier once positive relative excess exists; this shows why a late one-row trigger does not acquire that excess by ordinary Leavitt/Toeplitz direct-sum replication.
---

Let `H=C^d` and let

```text
A_0:H^(p_0)->H^(q_0),             p_0>q_0,
r_0=p_0-q_0.
```

Consider any balanced direct-sum recurrence obtained by replacing every
source and target block by `b_k>=1` unitarily conjugate copies and then adding
`s_k>=0` square source--target blocks.  Thus

```text
p_(k+1)=b_k p_k+s_k,
q_(k+1)=b_k q_k+s_k,
r_(k+1)=p_(k+1)-q_(k+1)=b_k r_k.                       (BSD1)
```

Then

```text
r_(k+1)/p_(k+1)<=r_k/p_k,                              (BSD2)
```

and hence `r_k/p_k<=r_0/p_0` at every depth.  In the pure-copy case
`s_k=0`, equality holds at every depth.

The same statement holds for the actual kernel density, not only the
rank--nullity lower bound.  If the added square blocks are injective, then

```text
dim ker(A_(k+1))/(p_(k+1)d)
 <= dim ker(A_k)/(p_k d),                              (BSD3)
```

with equality in the pure-copy case.  Arbitrary square blocks can add their
own kernels, but those are new deficiencies rather than amplification of the
triggered one.

Normalized Hilbert--Schmidt return error is also unchanged by pure
replication.  Let `P_k` be the kernel projection and suppose the branch
conjugacies intertwine one common return unitary `V` (the most favorable case
for the proposed construction).  If `A_(k+1)` is the direct sum of `b_k`
copies of `A_k`, then

```text
||(I_(p_(k+1)) tensor (V-1))P_(k+1)||_(2,p_(k+1)d)^2
 =||(I_(p_k) tensor (V-1))P_k||_(2,p_kd)^2.            (BSD4)
```

More generally it is the source-dimension-weighted average of the child
errors.  Repetition therefore neither increases kernel density nor decreases
normalized return error.

## Proof

Equation `(BSD1)` is immediate from balanced copying.  Therefore

```text
r_(k+1)/p_(k+1)
 =b_k r_k/(b_k p_k+s_k)
 <=r_k/p_k,
```

which proves `(BSD2)`.  Kernels and their dimensions add under orthogonal
direct sums, proving `(BSD3)`.  Squared unnormalized Hilbert--Schmidt norms
also add under direct sums, while the normalization divides by the total
source dimension.  For equal copies numerator and denominator are both
multiplied by `b_k`, proving `(BSD4)`.

## Consequence for a late missing row

Suppose the dimension tape first triggers at depth `n` and its whole
activated pencil has one missing row:

```text
p_0=p(n),             q_0=p(n)-1.
```

Every balanced binary, Leavitt, Toeplitz, or finite-branch direct-sum
descendant still has guaranteed relative excess exactly `1/p(n)` (or less
after square padding).  If `p(n)->infinity`, this is the cyclic-shift dilution
regime of `adaptive-rectangular-kernel-column-extraction`; it cannot feed the
positive-mass Fejer endpoint.

There are only two algebraic ways out of this calculation:

1. create new deficient rows at positive rate, rather than copy the one old
   defect; or
2. select the deficient summand and replicate it faster than the good
   summands.

The second operation is not ordinary self-similar direct sum.  It requires an
authenticated bad-summand selector.  If that selector is already controlled
in normalized Hilbert--Schmidt norm, it is precisely the matrix-only decoder
which the adaptive-pencil route is trying to construct.  The first operation
is a positive-rate local code/PCP actuator.  Thus self-similarity can provide
the address space and free conjugate copies, but it cannot provide the
positive-rate replication step merely by iteration.

This also explains why using one common high-order return word does not alter
the ledger: common-word intertwining is exactly the favorable hypothesis in
`(BSD4)`, under which normalized error is conserved rather than amplified.
