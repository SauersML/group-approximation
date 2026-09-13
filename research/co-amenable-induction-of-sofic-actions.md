---
rg: 2
id: co-amenable-induction-of-sofic-actions
kind: claim
title: A transitive amenable action is sofic exactly when its restriction to a point stabilizer is sofic
distinct_from:
  gkp-sofic-action-toolkit: that imports GKP's positive results, locally finite stabilizers and permanence under restriction and orbits; this is an induction theorem at the opposite end, for co-amenable stabilizers, with no soficity assumption on the actor.
  elek-szabo-sofic-permanence: that is soficity of groups under amenable extensions; this is the set-action analogue, where a point stabilizer replaces the normal subgroup and an amenable coset space replaces the amenable quotient group.
  amenable-action-of-a-sofic-group-need-not-be-sofic: that shows amenability of the action is not enough; this names exactly what has to be added, soficity of the stabilizer's action on the same set.
---

ESTABLISHED (unreviewed).

**Theorem.** Let `H` be a countable group and `alpha : H ↷ X` a transitive
action on a countable set. Fix `x_0 in X` and put `K = Stab_H(x_0)`. Suppose
`alpha` is amenable, i.e. `ell^infinity(X)` has an `H`-invariant mean. Then

```text
alpha is sofic    <=>    alpha|_K : K ↷ X is sofic,
```

where soficity is GKP Definition 2.1(5). Soficity of `H` is not assumed.

DERIVATION [[co-amenable-induction-of-sofic-actions-proof]].

## Corollaries

1. **Wreath products.** Let `L` and `H` be sofic groups and `K <= H`
   co-amenable, and suppose `K ↷ H/K` is sofic. Then `L wr_(H/K) H` and
   `L wr^*_(H/K) H` are sofic, by GKP Theorems 3.6 and 3.7
   ([[gkp-wreath-permanence-theorem]], [[gkp-free-generalized-wreath-soficity]]).
2. **Amenable image.** Suppose `K` contains a normal subgroup `N` of `H`
   with `H/N` amenable. Then `K ↷ X` factors through the amenable group
   `K/N`, so it is sofic by GKP Theorem 2.17 and Proposition 2.15(1). The
   theorem then gives `alpha` sofic, which also follows from Theorem 2.17
   applied to `alpha` itself.
3. **The counterexample, explained.** In
   [[amenable-action-of-a-sofic-group-need-not-be-sofic]] the stabilizer
   `K = Gamma_0 x directSum_(n>=1) G_n` contains `G_1`. The stabilizer of
   `tK` in `G_1` is `G_1 ∩ tKt^-1 = Gamma_1`, so `K ↷ X` has the Kun--Thom
   action `G ↷ G/Gamma` as a sub-orbit and is nonsofic, as the theorem
   requires.
4. **The Mikhailova edge.** For the Mikhailova subgroup `M = M_Q <= F x F`,
   the action of `M` on `(F x F)/M ~= Q` is
   `(u,v).q = phi(u) q phi(v)^-1 = phi(u) q phi(u)^-1`
   ([[mikhailova-coset-action-is-two-sided-q-action]]). This is the
   conjugation action of `Q`, pulled back along `(u,v) |-> phi(u)`. The
   theorem applies only when `Q` is amenable, which is exactly when the edge
   is co-amenable. In that case both sides hold (GKP Theorem 2.17).

## Novelty (bounded check)

GKP (arXiv:2401.04945v3, p. 8) settle locally finite stabilizers and write
that they "are unable to settle the more general case of amenable
stabilizers". The Section 2 statements recorded in this graph are Theorems
2.14, 2.17 and 2.19, Propositions 2.15 and 2.16, and the p. 8 remark. None of
them is a co-amenable statement. The later Gao--Patchell--Kunnawalkam
Elayavalli graph-action paper (arXiv:2408.15470) was not checked.

The proof is the Følner-times-model construction behind Elek--Szabó's
amenable-extension theorem, transplanted to set actions. The labelling that
GKP Definition 2.1(3) requires is carried by the stabilizer's model and
transported through a section cocycle.
