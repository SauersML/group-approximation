---
rg: 2
id: centralizing-hnn-perturbed-edge-separation
kind: claim
title: Approximate edge models separate the centralizing HNN rope
distinct_from:
  centralizing-hnn-sofic-via-regular-edge-centralizer: that excludes quotient models with exact edge centralization and computes their finite-image centralizer; this asks for approximate edge commutation and separation, without requiring the base to leave quotient models.
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

This proposed route seeks models genuinely non-quotient on `K_e`.
That is a design choice, not a necessary consequence of
[[centralizing-hnn-sofic-via-regular-edge-centralizer]]. The latter
excludes finite-quotient base models only when the stable letter
**exactly centralizes the whole finite edge image**. It does not exclude
finite-quotient base models with merely approximate commutation on a
tested edge generating set, as allowed in condition 1 here.

The proposed construction perturbs the edge/base model away from exact
quotient models. To use a wreath-product edge centralizer afterwards,
one would first need an exact free action of an appropriate finite edge
image; approximate freeness does not automatically supply that
centralizer. Alternatively one could construct a stable letter only
approximately centralizing the tested edge elements. Neither construction
nor the subsequent uniform Britton separation estimate is established here.

## Attempts

- **Exact quotient bases with exact edge centralization.** This joint
  model class fails by the no-go theorem. Exact quotient bases with
  approximately edge-centralizing stable letters are not excluded.
- **Random stable letters in the original exact centralizer.** For a
  nonseparable edge these cannot separate closure pinches at all, regardless
  of the distribution; it is not merely a missing independence estimate.
- **Deferred live lane.** Find models meeting conditions 1--2, either by
  a justified non-quotient construction or by approximate centralization
  in quotient models. A vanishing perturbation of all generator images
  in the old exact models cannot separate a fixed collapsed word by a
  positive amount: fixed-word evaluation is Lipschitz in those errors.
