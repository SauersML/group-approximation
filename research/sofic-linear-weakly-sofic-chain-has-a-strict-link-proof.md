---
rg: 2
id: sofic-linear-weakly-sofic-chain-has-a-strict-link-proof
kind: route
title: Two established inclusions and the weakly sofic separation force one strict link
target: sofic-linear-weakly-sofic-chain-has-a-strict-link
requires:
  - sofic-implies-linear-sofic-over-every-field
  - linear-sofic-implies-weakly-sofic-over-every-field
  - weakly-sofic-not-sofic
---

Fix a field `F`. Write `S`, `L_F` and `W` for the classes of countable
groups that are sofic, `F`-linear sofic, and weakly sofic.

1. `S ⊆ L_F` by `sofic-implies-linear-sofic-over-every-field`.
2. `L_F ⊆ W` by `linear-sofic-implies-weakly-sofic-over-every-field`.
3. `S ≠ W` by `weakly-sofic-not-sofic`: the Kun--Thom wreath is weakly
   sofic and not sofic.

Suppose both inclusions in 1 and 2 were equalities. Then `S = L_F = W`,
which contradicts 3. So `S ⊊ L_F` or `L_F ⊊ W`. The field `F` was
arbitrary. ∎

The target node already stated this argument in prose and said
"ESTABLISHED", but it had no route, so the graph listed it as OPEN. This route
lands the argument unchanged. Which link is strict is not decided here. For
the Kun--Thom wreath it is exactly the open pair
`kun-thom-wreath-linear-sofic` / `kun-thom-wreath-not-linear-sofic`.
