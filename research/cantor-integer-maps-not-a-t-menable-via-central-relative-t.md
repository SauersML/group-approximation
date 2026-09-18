---
rg: 2
id: cantor-integer-maps-not-a-t-menable-via-central-relative-t
kind: route
title: "Relative (T) for the central cyclic subgroup blocks every proper cnd function"
target: cantor-integer-maps-by-v-are-not-a-t-menable
requires:
  - cantor-integer-maps-central-direction-has-relative-t
---

Let `G = C(C,Z) ⋊ V`. Suppose `G` had the Haagerup property, and let `ψ` be a proper cnd
function on `G`, so that `{g : ψ(g) ≤ R}` is finite for every `R`.

The subgroup `<1_C>` is infinite, since `M·1_C ≠ 0` for `M ≠ 0`. A proper function is therefore
unbounded on it. This contradicts `cantor-integer-maps-central-direction-has-relative-t`.
