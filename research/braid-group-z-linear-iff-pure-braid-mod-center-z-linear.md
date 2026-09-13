---
rg: 2
id: braid-group-z-linear-iff-pure-braid-mod-center-z-linear
kind: claim
title: B_n embeds in some GL_m(Z) iff P_n modulo the full twist does
---

For every `n >= 2` the following are equivalent:

1. `B_n` has an injective homomorphism into some `GL_m(Z)`;
2. the pure braid group `P_n` does;
3. `P_n / <Delta^2>` does, where `Delta^2` is the full twist.

Moreover `P_n = U_n × <Delta^2>` internally, with `U_n` the kernel of the map
`P_n -> P_2 ≅ Z` that forgets strands `3, ..., n`. So `P_n / <Delta^2> ≅ U_n`
is a subgroup of `P_n`.

For `n >= 3`, `<Delta^2>` is the center of `B_n` and of `P_n` (Chow, 1948), and
`P_n / <Delta^2>` is the pure mapping class group of the sphere with `n + 1`
punctures (classical; not used here). For `n = 4` the Artin combing gives
`P_4 / <Delta^2> ≅ F_3 ⋊ F_2`, so the first open case of Problem 3.2 is the
Z-linearity of this free-by-free group.

Proof: `braid-group-z-linear-iff-pure-braid-mod-center-z-linear-proof`.
