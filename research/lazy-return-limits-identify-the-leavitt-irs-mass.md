---
rg: 2
id: lazy-return-limits-identify-the-leavitt-irs-mass
kind: route
title: Recover the whole-group atom of an IRS from lazy return probabilities
target: leavitt-invariant-random-subgroups-are-trivial-mixtures
requires:
  - leavitt-root-fixed-projections-equal-the-global-fixed-projection
  - binary-leavitt-elementary-group-is-simple
artifacts:
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

An invariant random subgroup `mu` has the character
`phi_mu(g)=mu({K:g in K})`. The first prerequisite makes this
`b*1+(1-b)*delta_1` for the binary Leavitt unit group.

Choose a lazy symmetric full-support probability `nu` on the
countable group. In each quasi-regular representation on
`l^2(H/K)`, its averaging operator is a positive contraction.
Its powers converge strongly to the fixed-vector projection,
so the return probability `nu^(convolution n)(K)` converges
to `1/[H:K]`, interpreted as zero for infinite index.

Integrating and using the character formula gives

```text
b = integral 1/[H:K] dmu(K).
```

The group is infinite, and simplicity rules out proper
finite-index subgroups. The integral is therefore `mu({H})`.
For every nonidentity `g`, the event that a proper subgroup
contains `g` has measure `phi_mu(g)-mu({H})=0`. Countability
leaves only the subgroups `{1}` and `H` almost surely.

The stabilizer map of a probability-preserving action has an
invariant random subgroup law. Applying the classification to
that law gives the asserted free/global-fixed decomposition.
The proof needs no uniform return-probability rate and no
injectivity theorem for the IRS-to-character map.
