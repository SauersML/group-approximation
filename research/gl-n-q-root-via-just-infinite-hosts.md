---
rg: 2
id: gl-n-q-root-via-just-infinite-hosts
kind: route
title: Pass to the simple inputs SL_m(Q), m odd, and upgrade a just-infinite finitely presented host to a finitely presented simple one
target: gl-n-q-embeds-in-fp-simple-group
requires: [sl-odd-q-simple-inputs-for-gl-n-q-root, simple-group-in-fp-simple-iff-fp-just-infinite-host, sl-odd-q-has-fp-just-infinite-host]
---

Let `n >= 2`. By `sl-odd-q-has-fp-just-infinite-host`, pick an odd `m >= n + 1`
with a finitely presented `Γ_m` and a nontrivial `ρ_m : SL_m(Q) -> Γ_m`, just-infinite
above its image. `SL_m(Q)` is infinite and simple
(`sl-odd-q-simple-inputs-for-gl-n-q-root`, clause 1). So
`simple-group-in-fp-simple-iff-fp-just-infinite-host` (2 ⇒ 1) embeds `SL_m(Q)` in a
finitely presented simple group `T`. Then `GL_n(Q) ↪ SL_m(Q) ↪ T` by clause 2. ∎
