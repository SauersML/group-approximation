---
rg: 2
id: leavitt-target-return-channel-count-firewall
kind: claim
title: Fewer than p squared target-return channels cannot source-saturate the Leavitt Reynolds range
distinct_from:
  target-saturated-reynolds-return-does-not-lock-leavitt-reservoir: that treats one returned contraction and separates source from target saturation; this proves the sharp channel-count law for arbitrary positive aggregates and rules out summing the two native branch returns.
  leavitt-branch-reynolds-return-has-rectangular-gap: that computes the exact leakage of one canonical branch return; this applies to every approximation-dependent family of contractions with the same source and target Reynolds supports.
  affine-leavitt-source-saturated-reynolds-checksum: that asks the full presentation to force one impossible source-saturated contraction and thereby contradict microstates; this proves that a positive aggregation of the two visible branch returns cannot be the mechanism forcing it.
---

**ESTABLISHED SHARP RANK FIREWALL.**  Let `R_s,R_t` be orthogonal
projections on one finite-dimensional Hilbert space of superoperators, with

```text
tr_ad(R_s)=p^(-2),             tr_ad(R_t)=p^(-4).       (TCF1)
```

No nesting assumption is needed.  Let `X_1,...,X_m` be arbitrary
approximation-dependent contractions satisfying

```text
X_j=R_t X_j R_s,              ||X_j||_op<=1.           (TCF2)
```

For arbitrary weights `alpha_j>=0`, positivity and `(TCF2)` give

```text
X_j X_j^*<=R_t,
tr_ad(X_j^*X_j)=tr_ad(X_jX_j^*)<=p^(-4),               (TCF3)
```

and hence

```text
tr_ad(sum_j alpha_j X_j^*X_j)
 <=p^(-4)sum_j alpha_j.                                (TCF4)
```

Consequently, if a unit-weight sum covers the source Reynolds trace up to
`epsilon`,

```text
tr_ad(sum_j X_j^*X_j)>=p^(-2)-epsilon,                 (TCF5)
```

then necessarily

```text
m>=p^2-epsilon p^4.                                    (TCF6)
```

In particular the two native Leavitt branches satisfy, for every choice of
their returned coordinate maps,

```text
tr_ad(X_0^*X_0+X_1^*X_1)<=2p^(-4)<p^(-2)              (TCF7)
```

for every `p>=2`.  Their aggregate leaves the fixed normalized trace deficit

```text
p^(-2)-2p^(-4)>0.                                      (TCF8)
```

This is not an artifact of estimating the channels separately.  Every
coherent linear combination which is itself a contraction supported from
`R_s` to `R_t` still obeys `(TCF3)` and has trace at most `p^(-4)`.

The threshold `p^2` is sharp from support and contraction data alone.  Since
`rank(R_s)=p^2 rank(R_t)`, decompose

```text
Ran(R_s)=H_1 direct_sum ... direct_sum H_(p^2),
dim H_j=rank(R_t).
```

Choose a unitary `V_j:H_j -> Ran(R_t)` and extend it by zero.  Then

```text
X_j=V_j P_(H_j),
X_j^*X_j=P_(H_j),              X_jX_j^*=R_t,
sum_(j=1)^(p^2) X_j^*X_j=R_s.                          (TCF9)
```

Thus an argument using only target support, contraction, positivity, and a
finite sum of return energies cannot do better than `(TCF4)`.  Below `p^2`
channels it cannot source-saturate; at `p^2` channels the exact rectangular
geometry already admits a perfect abstract return frame and supplies no
contradiction.

Applied to the affine-Leavitt checksum route, this eliminates a natural
escape from the failed single-branch formula: the range-sum identity has two
native branches, but adding their positive Gram returns cannot approach the
source density `p^(-2)`.  A successful proof must use a payload-coupled
relation which makes one returned channel violate the target rank ceiling
(thereby directly contradicting finite matrices), rather than recover the
source by ordinary branchwise energy aggregation.
