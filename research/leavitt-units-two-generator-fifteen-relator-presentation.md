---
rg: 2
id: leavitt-units-two-generator-fifteen-relator-presentation
kind: claim
title: The binary Leavitt unit group has a presentation with two generators and fifteen relators
distinct_from:
  thompson-steinberg-three-generator-presentation: that is the three-generator, sixteen-relator form it is derived from, total length 467; this merges v and x into one generator w, so it has one generator and one relator fewer, but total length 1267.
  thompson-steinberg-presentation-of-leavitt-unit-group: that is the four-generator, eighteen-relator form over Bleak--Quick's three-generator V, the shortest in total length; this minimizes the number of generators instead.
---

**ESTABLISHED (2026-09-12, unreviewed)** through
`leavitt-units-two-generator-fifteen-relator-presentation-proof`.

`L_(F_2)(1,2)^x = <u, w | 15 relators>`, total literal length 1,267, longest 196, with
```text
u -> t_(00,01) t_(10,110) t_(10,111)            (Bleak--Quick's u)
w -> v . (1 + S[0000]T[001])                    (v = (01 10 11), maps on the right)
```
The relators are the sixteen of `thompson-steinberg-three-generator-presentation`, with
`v -> w^-2` and `x -> G^-1 w^3 G` substituted, where
`G = u w^2 u^-1 w^-2 u^2 w^2 u^-1 w^2`
is the Bleak--Quick word `u v^-1 u^-1 v u^2 v^-1 u^-1 v^-1` after that substitution. One relator
is dropped: `x^2` becomes a conjugate of `w^6`, which is the inverse of the image `w^-6` of
`v^3`. The literal words are in
`experiments/nonsofic-certificates/presentations/two-generator-presentation.json`.

Two generators is the minimum for a noncyclic group. So `L_(F_2)(1,2)^x` — finitely presented,
simple, nonsofic, Kazhdan, with full MF radical — is a two-generator group with an explicit
fifteen-relator presentation. Its deficiency is `-13`. The only bound known here comes from
`H_1 = H_2 = 0`: deficiency at most `0`.
