---
rg: 2
id: mikhailova-left-right-action-current-frontier
kind: claim
title: The Mikhailova left-right action is an intrinsic free-cover problem not decided by the commuting-action counterexample
distinct_from:
  mikhailova-central-rope-is-a-left-right-action-wreath: that identifies the rope with the free wreath over this action; this determines what is known and what remains open about the action itself.
  commuting-sofic-actions-need-not-combine: that gives a nonsofic combined action with diagonal stabilizer inside a Kazhdan pair; it does not decide the pullback of the full diagonal action through a free presentation.
  mihailova-left-right-local-models-do-not-see-q: that proves arbitrary finite metric patches exist; this records the exact finite-Schreier boundary and the surviving positive-density Hamming condition.
---

Let `q:F_m->H` be an epimorphism, `N=ker(q)`, and

```text
M_H={(u,v) in F_m x F_m:q(u)=q(v)}.
```

Under `(F_m x F_m)/M_H isomorphic to H`, the coset action is

```text
(u,v).h=q(u)h q(v)^(-1).                              (MLF1)
```

The following boundary is established.

1. Soficity of `(MLF1)` is independent of the chosen finite free presentation of `H`.
2. `(MLF1)` has exact finite Schreier models separating every finite orbit packet if and only if `H` is residually finite. Equivalently, `M_H` is separable in `F_m x F_m` if and only if `H` is residually finite.
3. Consequently the compiler's non-residually-finite `H` cannot be handled by finite quotients or exact finite actions. Alekseev--Thom local metric models do not improve this: they exist for every `H`.
4. The Kun--Thom counterexample to combining commuting sofic actions does not imply that `(MLF1)` is nonsofic. Its stabilizer is `Delta Gamma < G x G` for an infranormal Kazhdan subgroup `Gamma<G`; here the stabilizer is the full inverse image `(q x q)^(-1)(Delta H)`. Nonsoficity does not descend from the quotient actor `H x H` to its free cover, even when `H` is finitely presented; each coordinate restriction is a sofic free-group action.
5. Nor can one replace the missing argument by correcting the actor maps to exact finite actions: Ioana proved that `F_m x F_m` for `m>=2` is not even very flexibly permutation stable. This does not prove `(MLF1)` sofic; it proves that the exactification step needed by that proposed obstruction is unavailable.

Thus for the fixed nonsofic property-`(T)` Mikhailova quotient used in the repository, soficity of `(MLF1)` remains **OPEN**. The exact unresolved datum is a GKP positive-density Hamming orbit-chart witness for the single stabilizer `M_H`. No current theorem promotes the separate free coordinate charts, the universal local metric models, or approximate commuting actor permutations to that witness.

DERIVATION
[[mikhailova-left-right-frontier-proof]]
