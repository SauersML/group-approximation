---
rg: 2
id: regularized-anchor-square-function-has-dimension-free-cut
kind: claim
title: The averaged anchor-odd square function has a dimension-free regularized cut
distinct_from:
  join-of-odd-cuts-softens-an-entire-anchor-row: that takes the literal join of all individual hard cuts and obtains pointwise softness but no boundary bound; this thresholds their averaged positive operator and obtains a quantitative boundary bound without a frame condition number.
  one-anchor-odd-spike-has-a-cheap-reducing-cut: that thresholds one site square and pays one pair of commutator rows; this thresholds the whole anchor row and pays only the global pair energy and the anchor row norm.
  covariant-square-function-has-common-reducing-threshold: that is the abstract coarea theorem; this constructs the required covariant positive contraction from the complete-pair overlay and computes all constants.
---

ESTABLISHED.  Let `Q_1,...,Q_L` be reflections in a finite tracial von
Neumann algebra.  For a fixed anchor `a` put

```text
 Y_(a,i)=(Q_i-Q_aQ_iQ_a)/2,
 R_(a,i)=Y_(a,i)^2,
 K_a=(1/L)sum_i R_(a,i),
 q_a^2=(1/L)sum_i ||[Q_a,Q_i]||_2^2,
 E_pair=(1/L^2)sum_(i,j)||[Q_i,Q_j]||_2^2.             (RAC1)
```

Then `0<=K_a<=1`, `K_a` commutes with `Q_a`, and

```text
 tau(K_a)=q_a^2/4,                                     (RAC2)
 (1/L)sum_l ||[K_a,Q_l]||_2
       <=2(q_a+sqrt(E_pair)).                           (RAC3)
```

Consequently, for every `0<theta<1/2` there is a threshold
`t_a in [theta,2theta]` such that, with

```text
 p_a=1_[t_a,1](K_a),       q=1-p_a,
 D(p_a)=(1/L)sum_l||[p_a,Q_l]||_2^2,
```

one has

```text
 tau(p_a)<=q_a^2/(4theta),                              (RAC4)
 D(p_a)<=2(q_a+sqrt(E_pair))/theta,                     (RAC5)
 qK_aq<=2theta q.                                       (RAC6)
```

The cut commutes with the anchor, so resetting
`Q_a'=p_a+qQ_a` is an exact reflection and costs

```text
 ||Q_a-Q_a'||_2^2=4tau(p_a(1-Q_a)/2)<=q_a^2/theta.     (RAC7)
```

Averaging over a uniformly random anchor gives

```text
 E_a tau(p_a)<=E_pair/(4theta),
 E_a D(p_a)<=4sqrt(E_pair)/theta,
 E_a ||Q_a-Q_a'||_2^2<=E_pair/theta.                   (RAC8)
```

Thus the literal noncommuting join is unnecessary for the row-column
Newton estimate: on the retained block, the averaged odd square function
itself has operator norm at most `2theta`.  This is precisely the
dimension-free row norm entering dense bilinear estimates.  The result does
not by itself produce an exact reducing block.  Either the off-diagonal
leakage `D(p_a)` must be carried as an `L_2` remainder, or cosine--sine
block diagonalization must be shown not to recreate an operator-norm spike
on the retained block.
