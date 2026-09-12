---
rg: 2
id: tensor-spectator-defeats-three-gauge-tests-proof
kind: route
title: Amplify the Pauli-reservoir pair by an invisible matrix factor
target: three-gauge-tests-leave-a-tensor-spectator
requires: []
---

Write normalized trace as the tensor product of the normalized traces.  For
`T_1=T_2=1`, the cross-Gram contraction is `R=T_2^*T_1=1`, so

```text
Delta=tau(P)-tau(R^*R)=0.
```

Its polar unitary is `V=1`, whence `[V,X]=[V,Z]=0`.  All conditions hold on
the same corner, of normalized trace one.  The displayed commutants follow
from the elementary tensor identity

```text
(M_a tensor I_b)' = I_a tensor M_b.
```

Since `s>=2`, the third factor supplies non-scalar elements in both excess
commutants and outside the joint algebra, proving all three strict failures.

For completeness, joint fullness is sufficient in the exact commuting
setting.  If `A` and `B` commute and generate the full corner, then every
central projection of `A` commutes with both and is central in the generated
full matrix algebra, so `A` is a factor.  After a unitary conjugacy,
`A=M_r tensor I_k` and `A'=I_r tensor M_k`.  Because `B subset A'` and
`A vee B=M_r tensor B` is the full matrix algebra, `B=A'`; taking commutants
gives `B'=A`.

The sharp combined positive statement from the three analytic tests is only
a gauge estimate.  The polar lemma supplies `V` with
`||T_1-T_2V||_2<=sqrt(2Delta)`, while Pauli averaging supplies a unitary
`U in {X,Z}'` with
`||V-U||_2<=||[V,X]||_2+||[V,Z]||_2`.  Contractivity of `T_2` therefore gives

```text
||T_1-T_2U||_2
 <= sqrt(2Delta)+||[V,X]||_2+||[V,Z]||_2.
```

No term in this bound measures the spectator algebra.
