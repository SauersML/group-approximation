---
rg: 2
id: mikhailova-central-rope-is-a-left-right-action-wreath
kind: claim
title: The Mikhailova central rope is a free wreath over the quotient left-right action
distinct_from:
  centralizing-hnn-perturbed-edge-separation: that asks for direct Britton-separating permutation models; this identifies the exact set action whose soficity would supply the standard free-wreath route.
  mihailova-left-right-local-models-do-not-see-q: that treats weak local metric models; this concerns the positive-density permutation approximation problem for the combined left-right action.
---

**ESTABLISHED REDUCTION.**  For every subgroup `L<=K`,

```text
<K,v | [v,L]=1>
  ~= ( *_(K/L) Z ) semidirect K,
```

where `K` translates the free factors through its action on `K/L`.
This is the free generalized wreath product for the coset action.

For the compiler's Mikhailova factor

```text
K_0=F x F(X) x F(X),   L_0=F x M_H,
```

the irrelevant first coordinate cancels and the coset action is exactly

```text
F(X) x F(X) acts on H,
(p,q).h = pbar h qbar^(-1).                           (MLW1)
```

Thus the central-rope permanence problem reduces to the combined left-right
action on `H`, together with the standard graph-witness factor.  Soficity
of each coordinate action separately does not by itself give a sofic model
of the combined commuting action.  This node asserts only the exact
structural reduction; it does not assert that `(MLW1)` is sofic or
nonsofic.

DERIVATION
[[mikhailova-central-rope-left-right-wreath-proof]]
