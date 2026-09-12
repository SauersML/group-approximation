---
rg: 2
id: qpcp-from-global-walk-reduction
kind: route
title: Iterate global tensor amplification with a reducer whose loss is below its linear gain
target: quantum-pcp-constant-gap-local-hamiltonian
requires:
  - global-walk-linearly-amplifies-hamiltonian-energy
  - global-walk-reducer-has-net-energy-gain
  - bmvz-iterable-tensor-gap-amplification
artifacts:
  - research/artifacts/qpcp-global-walk-amplification-2026-09-11.md
---

Use only the exponentially complete 5-local hardness starting family from
the BMVZ prerequisite; the amplifier here is the separately proved global
walk. Set `g=(3t+2)/(16L)>1` and `b=1/(2L)`. One amplify/reduce step gives
NO energy at least `min{g epsilon,b}`. Starting at inverse-polynomial
NO energy, `O(log n)` steps reach `b`.

On YES instances, one step costs at most the fixed multiplier `At` and
the additive error `2^(-n_i)`. The reducer never decreases the site count;
after padding the seed, `n_i>=n`. Hence after `ell=O(log n)` rounds the
YES energy is at most

```text
max{1,At}^ell (a_0+ell 2^(-n)),
```

which is negligible. Constant locality is restored each round, the local
dimension remains two, and the reducer's bounds put term count, sites
and maximum term-description bit length under one fixed linear recurrence.
They remain polynomial through `O(log n)` rounds, as does total running
time. This gives a constant relative promise gap in the
normalized local Hamiltonian form. Section 5 of the artifact carries
the full bookkeeping. No locality reducer is constructed by this route.
