---
rg: 2
id: clifford-packets-are-stationary-for-intrinsic-green-step
kind: claim
title: Clifford packets are stationary for the intrinsic finite-Green step
distinct_from:
  balanced-parity-excludes-perfect-matching-pauli-mixtures: that charges a central mixture of matched Pauli pairs by balanced parity; this is a direct stationary-point obstruction for the new intrinsic correction map.
  intrinsic-finite-green-commutator-step-has-the-correct-tangent: that proves strict derivative contraction at commuting code points; this shows no base-free PL inequality can hold on the whole reflection space.
  regularized-anchor-square-function-has-dimension-free-cut: that quarantines high averaged odd square function; this proves that quarantine is logically necessary before intrinsic Green descent.
---

ESTABLISHED SHARP OBSTRUCTION.  Let `Q_1,...,Q_L` be pairwise
anticommuting Clifford reflections.  For `i!=j`,

```text
 (Q_iQ_j)^2=-I,
 beta_ij=(I-(Q_iQ_j)^2)/2=I.                           (CGS1)
```

Hence every `c_i=L^(-1)sum_j beta_ij` is a scalar positive operator.  Every
current pinching map fixes it, so the Green output `g_i` is selfadjoint and
the skew tangent generator `(g_i-g_i^*)/4` vanishes.  Therefore

```text
 F_K(Q)=Q                                                     (CGS2)
```

for every finite `K`, while

```text
 E_pair=(1/L^2)sum_(i,j)||[Q_i,Q_j]||_2^2=4(1-1/L).    (CGS3)
```

Thus no global Polyak--Lojasiewicz inequality can lower-bound the intrinsic
correction row by complete-pair energy.

The obstruction persists at arbitrarily small normalized-HS energy: take a
central direct sum of trace `alpha` carrying the Clifford packet and a
commuting exact tuple on the complement.  Both the pair energy and the
distance of a cheap reset are `Theta(alpha)`, but the intrinsic correction
still vanishes on the Clifford summand.

This does not obstruct the regularized-cut program.  On the Clifford block,
for every anchor `a` and `i!=a`, `Y_(a,i)^2=I`; hence

```text
 K_a=(1/L)sum_iY_(a,i)^2=(1-1/L)I.                    (CGS4)
```

Every aggregate threshold below `1-1/L` quarantines the whole stationary
packet at trace cost `alpha`.  Therefore the base-free coercivity target for
the intrinsic step must be stated only after the aggregate high-`K_a`
sector has been removed and balanced parity has paid sparse stationary
packets.  A global pair-energy-only PL inequality is false.
