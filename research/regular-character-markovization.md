---
rg: 2
id: regular-character-markovization
kind: claim
title: Every regular hyperlinear finite table admits a multiplicative doubly stochastic model
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

**Major positive gate.** For every finite multiplication table `T` and every
`eps>0`, there is `delta>0` such that any unitary model of `T` with normalized-
HS multiplication defect `<delta`, identity defect `<delta`, and regular-trace
separation `<delta` yields, on some finite state space allowed to depend on the
**whole table**, doubly stochastic matrices `{P_g}` satisfying

```text
||P_g P_h-P_{gh}||_{2}<eps        on tested products,
||P_e-I||_{2}<eps,
|tau(P_g)|<eps                    on tested g != e.
```

The output need not be a pointwise function `U -> P_U`, need not use the same
dimension, and may introduce hidden/context variables. This table-dependent
freedom is essential because Cairn already rules out universal pointwise
unitary-to-permutation rounding.

By `markov-sofic-equals-sofic`, this claim is sufficient for every hyperlinear
group to be sofic. It is sharper than a common-Cartan theorem: once a
multiplicative Markov table exists, inverse relations force the final
permutation integrality automatically.

## Attempts

- **Entrywise dephasing.** Dead before rounding: `dephasing-destroys-multiplicativity`.
  The stronger `dephasing-inverse-forces-monomial` shows that even preserving
  inverse composition in one basis would already force near monomiality.
- **Fresh random intermediate bases.** Dead in expectation:
  `haar-random-basis-depolarization` gives the exact depolarizing channel and
  retains only `1/(d+1)` of the coherent transition.
- **Heat/entropic smoothing of a discretized action.** Does not remove the
  gate: if the smoothed Markov kernels also satisfy inverse products near `I`,
  `birkhoff-approx-inverse-permutation` drives them back toward deterministic
  permutations. The smoothing still has to solve the same joint integrality
  problem.
- **Independent generator discretizations.** Pairwise good kernels need not
  live on a common latent state space and need not compose. The surviving
  routes below are deliberately whole-table/contextual.
