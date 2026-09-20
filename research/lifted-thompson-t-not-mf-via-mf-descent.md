---
rg: 2
id: lifted-thompson-t-not-mf-via-mf-descent
kind: route
title: The lifted Thompson group is not MF once T is not MF and MF-ness of T-bar descends to T
target: lifted-thompson-t-is-not-mf
requires:
  - thompson-t-has-full-mf-radical
  - lifted-thompson-t-mf-descends-to-t
  - lifted-thompson-t-mf-radical-dichotomy
---

**Proof.**
1. By `thompson-t-has-full-mf-radical`, `T` is not MF, since `T != 1`.
2. By the contrapositive of `lifted-thompson-t-mf-descends-to-t`, `T̄` is
   not MF.
3. By item 1 of `lifted-thompson-t-mf-radical-dichotomy`,
   `Rad(T̄) = T̄`.  In particular `z in Rad_MF(T̄)`.

∎

## Relation to the eigencorner route

`lifted-thompson-t-not-mf-via-central-eigencorners` has the same first
prerequisite.  Its second one,
`lifted-thompson-t-centre-has-commutant-eigencorners`, implies the second
one here (route `lifted-thompson-t-mf-descent-via-central-eigencorners`).
So this route is never worse.  Its open leaf quantifies existentially over
representations ("one scalar twist somewhere"), where (EC) quantifies
universally ("an eigencorner in every representation").

The decomposition is exact:
`lifted-thompson-t-is-not-mf <=> thompson-t-has-full-mf-radical AND lifted-thompson-t-mf-descends-to-t`.
The two prerequisites fail in disjoint worlds.  If `T` is MF, the second
holds automatically.
