---
rg: 2
id: lodha-moore-not-sofic-from-thompson-f-not-sofic
kind: route
title: Nonsoficity of Thompson's F passes up to the Lodha--Moore group
target: lodha-moore-group-is-not-sofic
requires:
  - thompson-f-is-not-sofic
  - thompson-f-is-a-subgroup-of-lodha-moore-group
  - elek-szabo-sofic-permanence
---

1. `F <= G_0`, by `thompson-f-is-a-subgroup-of-lodha-moore-group`.
2. Soficity passes to subgroups (Elek--Szabó Theorem 1, clause 1, in
   `elek-szabo-sofic-permanence`).
3. So a sofic `G_0` would make `F` sofic, contradicting `thompson-f-is-not-sofic`. ∎

The converse is not claimed: nonsoficity of `G_0` is not known to force
nonsoficity of `F`.  Through `left-orderable-non-sofic-via-lodha-moore-group`,
this route makes `thompson-f-is-not-sofic` enough for the left-orderable root.
