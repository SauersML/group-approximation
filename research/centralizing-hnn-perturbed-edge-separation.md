---
rg: 2
id: centralizing-hnn-perturbed-edge-separation
kind: claim
title: Perturbed non-quotient edge models separate the centralizing HNN rope
distinct_from:
  centralizing-hnn-sofic-via-regular-edge-centralizer: that claim proves the quotient-model no-go and computes the exact free-edge centralizer; this claim is the missing genuinely approximate separation theorem.
  sofic-safe-finite-presentation-compiler: that asks for the full two-rope compiler; this is only the inner centralizing HNN separation step.
---

Let `K_e` and its finitely generated Mikhailova-type subgroup `L_e` be the
base and edge of the positive-branch inner rope, and put

```text
Gamma_e = <K_e, v | [v,l]=1 for l in L_e>.
```

For every finite set `W` of nontrivial Britton-reduced words in `Gamma_e`
and every `epsilon>0`, there are a finite set `X`, an
`epsilon`-multiplicative permutation model of the required finite ball of
`K_e`, and a permutation `sigma_v` such that

1. every tested commutator `[sigma_v,pi(l)]`, `l in L_e`, has normalized
   Hamming defect at most `epsilon`; and
2. every `w in W` moves a dimension-independent positive fraction of `X`.

The model must be genuinely non-quotient on `K_e`.  By
[[centralizing-hnn-sofic-via-regular-edge-centralizer]], every model which
factors through a finite quotient kills `[v,k]` for each
`k in closure(L_e) \ L_e`, regardless of the choice of stable letter.

The proposed live construction perturbs a locally free edge action away
from quotient models and chooses `sigma_v` from its large wreath-product
edge centralizer.  What remains is a uniform Britton separation estimate
for the resulting correlated random permutation products.  Standard
independence estimates do not apply directly because the centralizer moves
whole edge orbits and its labels interact with the base action.

## Attempts

- **Exact quotient bases.**  This fails for a theorem, not a missing
  estimate: the established centralizer/no-go claim shows that every
  profinite-closure pinch is killed in every finite quotient.
- **Independent random stable letters.**  A generic random permutation does
  not approximately centralize the edge action.  Sampling inside the edge
  centralizer restores the relators but correlates orbit motion and labels,
  so the usual exposure martingale for independent random permutations does
  not give Britton separation.
- **Deferred live lane.**  Perturb the base model on a vanishing Hamming set
  so closure points separate while the edge remains locally free, then prove
  a correlated wreath-centralizer word estimate uniform over each fixed
  finite Britton packet.
