---
rg: 2
id: irreducible-normal-holonomy-extension-proof
kind: route
title: Quantize the induced invariant rank and identify its subgroup restriction
target: irreducible-normal-holonomy-has-uniform-extension-gap
requires:
  - moving-subgroup-schreier-correction-has-no-index-loss
---

Retain the induced representation `Pi` on `K`, isometry `W`, rank-`d`
projection `P=WW^*`, and invariant spectral projection `Q` from the proof
of the dependency. Its original-rank estimates give

```text
h^2:=||P-Q||_HS^2 <= 4 beta^2 d/kappa^2,
|rank(Q)-d| <= h^2,
||Pi(s)W-WU_s||_HS <= beta sqrt(d).                     (INP1)
```

Normality makes each coset summand invariant under `N`, and on the
summand indexed by `t` the restriction is

```text
n |-> pi(t^(-1) n t).
```

These representations are irreducible of dimension `d`. Complete
reducibility of finite-dimensional unitary representations therefore
implies that every `N`-invariant subspace of `K`, in particular `QK`, has
dimension divisible by `d`. If `beta<kappa/2`, `(INP1)` puts `rank(Q)`
strictly between `0` and `2d`. Hence `rank(Q)=d`.

Take the polar part of `QW` and extend it on its kernel to an isometry
`J:C^d->QK`, as in the dependency's proof. Equal projection ranks give

```text
h^2=2(d-Tr(PQ)),
||J-W||_HS^2 <= 2(d-Tr(PQ))=h^2.
```

Since `J` is now onto `QK`, put `alpha(g)=J^*Pi(g)J`. It is a genuine
representation on the original `C^d`, and

```text
||alpha(s)-U_s||_HS
 =||Pi(s)J-JU_s||_HS
 <= beta sqrt(d)+2||J-W||_HS
 <= (1+4/kappa) beta sqrt(d).                           (INP2)
```

It remains to identify the restriction, rather than merely its dimension.
We may take the identity as the representative of the coset `N`:
replacing its previous representative `a in N` by `1` and its gauge
`V_a` by `V_a pi(a)^*` preserves every edge norm. Indeed this is a change
of coset coordinates in the exact induced representation and its isometry.

Let `ev_1:K->C^d` be evaluation at that identity coordinate. On `QK`
it intertwines the `N` action with `pi`. It cannot vanish there. For any
representative `t` and `x in QK`, the identity coordinate of
`Pi(t^(-1))x` is exactly the `t` coordinate of `x`. Since `QK` is
`G`-invariant, vanishing of `ev_1` on `QK` would force all its coordinate
evaluations to vanish, contradicting `dim(QK)=d>0`.

The nonzero intertwiner `ev_1|_(QK)` is surjective because `pi` is
irreducible. Equal dimensions make it invertible; its polar part is a
unitary intertwiner. Therefore `alpha|_N` is unitarily equivalent to
`pi`. Conjugating `alpha` by that intertwiner gives an extension of `pi`;
the closeness estimate `(INP2)` remains asserted in the original basis.
Contraposition proves `(ING2)`.
