---
rg: 2
id: mihailova-nonseparable-coset-stabilizer
kind: claim
title: A Mihailova fiber product gives an effective nonseparable stabilizer in the replacement actor
distinct_from:
  graph-coset-mixed-module-is-sofic: that proves separability when projection to the virtually-free factor is injective; this stabilizer has a nontrivial vertical kernel and is explicitly nonseparable.
  coordinate-action-not-sofic: that imports nonsoficity of one arithmetic coset action; this proves only failure of residual finiteness for a new explicit coset action and does not silently promote it to nonsoficity.
  algebraic-compact-action-envelope-for-non-ce-relation: that requires the fixed non-CE factor to embed in an algebraic crossed product; this supplies an effective Haar coset-module candidate but not that embedding.
---

Let `Gamma_0` be the virtually-free Manzoor source actor.  There is an
explicit finitely generated subgroup

```text
P < Gamma_0 x SL_3(Z)                                  (MFP1)
```

which is not separable in the ambient group.  It can be chosen as follows.
Take a fixed finitely presented nonsofic group

```text
Q=<x_1,...,x_m | r_1,...,r_k>
```

from `finitely-presented-nonsofic-group-exists` (for example the published
Fournier--Facio witness), embed two copies of the rank-`m` free group into
`Gamma_0` and `SL_3(Z)`, and take the pullback of the diagonal subgroup of
`Q x Q`:

```text
P_Q={(u,v) in F_m x F_m : ubar=vbar in Q}.              (MFP2)
```

The generators

```text
(x_i,x_i)  (1<=i<=m),       (r_j,1)  (1<=j<=k)          (MFP3)
```

generate `P_Q`, so `(MFP1)` is effective and finitely generated.  It escapes
the injective-projection fence maximally:

```text
P_Q cap ({1} x F_m) = {1} x ker(F_m -> Q).
```

Since `Q` is nonsofic it is not residually finite.  The diagonal in `Q x Q`,
and hence `P_Q` in `F_m x F_m`, is nonseparable.  Nonseparability persists in
`Gamma_0 x SL_3(Z)`.

Consequently the transitive coset action on
`X=(Gamma_0 x SL_3(Z))/P` is not residually finite.  The compact Haar coset
module

```text
K=(Z/2)^X,
W=(direct_sum_X Z/2) rtimes (Gamma_0 x SL_3(Z))         (MFP4)
```

is effective: `W` is finitely generated and recursively presented.  This is
the first explicit mixed coset module in the replacement actor that survives
all separability and spectator fences.

It also survives the homoclinic-density screen for a structural reason.
`infinite-stabilizer-coset-bernoulli-has-trivial-homoclinic-group` gives
`Delta(K,Gamma_0 x SL_3(Z))={1}` because `P` is infinite.  Thus this is not a
dense-finite-support algebraic shift in disguise; the Hayes model-measure
criterion has no hypothesis to act on here.

No stronger conclusion is asserted.  In particular, nonseparability does not
by itself prove that the coset action is nonsofic, and nonsoficity of the
quotient `Q` cannot simply be pushed through the free-group kernels in
`(MFP2)`.  In fact Gao--Kunnawalkam Elayavalli--Patchell prove that **every**
action of a free group on a countable set is sofic, so each coordinate action
on `(Q x Q)/Delta Q` is sofic regardless of `Q`.  The combined `F_m x F_m`
action is not residually finite; deciding whether it is sofic is precisely a
commuting-actions problem.  Whether `L(W)` contains the fixed non-CE relation
factor (or is itself non-CE) is the remaining analytic question.

The weakest orbit-chart attack is now closed.
`mihailova-left-right-local-models-do-not-see-q` applies Alekseev--Thom to
show that the left-right action has finite local isometric models for every
quotient `Q`, because the actor `F_m x F_m` is residually finite.  This remains
true for the nonsofic `Q` used here.  Such models therefore cannot decide the
combined action.  What remains is exactly the upgrade from arbitrary finite
metric patches to positive-density Hamming orbit charts, or equivalently an
operator-level promotion toward finite-dimensional approximation of the
left-right representation on `ell^2(Q)`.
