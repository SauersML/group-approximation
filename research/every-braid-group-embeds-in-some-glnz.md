---
rg: 2
id: every-braid-group-embeds-in-some-glnz
kind: claim
title: Every braid group B_n has an injective homomorphism into some GL_m(Z)
distinct_from:
  spherical-artin-groups-are-linear-over-q-x-y: that is an established embedding of braid groups into GL_N over a field of transcendence degree 2; this asks for integer matrices, which forces a discrete image in GL_m(R).
---

For every `n >= 1` there is `m` and an injective homomorphism
`B_n -> GL_m(Z)`. This is the affirmative answer to Zaremsky Problem 3.2
(`zaremsky-3-02-braid-groups-embed-in-glnz`).

By `braid-groups-on-at-most-three-strands-embed-in-glnz` it holds for
`n <= 3`. By `braid-group-z-linear-iff-pure-braid-mod-center-z-linear` it is
equivalent to: for every `n`, `P_n / <Delta^2>` embeds in some `GL_m(Z)`.

## Attempts

1. **Specialize a faithful representation at algebraic units.** If
   `rho: B_n -> GL_m(Z[q^{±1}, t^{±1}])` is faithful (Lawrence–Krammer) and
   there are units `u, v` of the ring of integers `O_F` of a number field `F`
   such that the specialization `q -> u, t -> v` is still faithful, then
   `B_n <= GL_m(O_F) <= GL_(m[F:Q])(Z)` by restriction of scalars. Where it
   stands: faithfulness is known for algebraically independent parameters.
   The graph's Cohen–Wales import (`spherical-artin-groups-are-linear-over-q-x-y`)
   records that one parameter can be specialized to a real `r_0` with
   `0 < r_0 < 1`; if that allows algebraic `r_0`, units such as
   `(3 - sqrt 5)/2` qualify (check pending). For the remaining parameter, each
   nontrivial braid dies at only finitely many values, but the union of these
   exceptional sets is countable and nothing yet prevents it from containing
   every algebraic unit.
2. **Virtually embed `P_n` in a right-angled Artin group.** RAAGs embed in
   right-angled Coxeter groups (Davis–Januszkiewicz), whose Tits reflection
   representation has integer entries. So a finite-index subgroup of `P_n`
   inside a RAAG makes `B_n` Z-linear, by
   `torsion-free-virtually-z-linear-groups-are-z-linear`. Where it stands:
   `B_n` is not virtually cocompactly cubulated for `n >= 4` (Huang–Jankiewicz–
   Przytycki, Haettel; to be verified), so only embeddings with no cocompact
   special structure remain. Whether `P_n` is virtually RFRS, a necessary
   condition, is being checked in the literature.
3. **The case `n = 4`.** Equivalent to Z-linearity of
   `P_4 / <Delta^2> ≅ F_3 ⋊ F_2`. `B_4 / Z(B_4)` is also a finite-index
   subgroup of `Aut(F_2)` (Dyer–Formanek–Grossman; to be verified), so it is
   enough that `Aut(F_2)` has a finite-index subgroup in some `GL_m(Z)`.
