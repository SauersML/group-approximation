---
rg: 2
id: closed-mcg-bh-via-rational-projective-full-group
kind: route
title: If the integral projective full group of the rational Cantorization is finitely presented, closed-surface mapping class groups virtually embed in a finitely presented full clopen-transitive Cantor group
target: closed-mcg-virtually-embeds-in-fp-full-cantor-group
requires:
  - closed-mcg-embeds-in-rational-projective-full-group
  - rational-projective-full-groups-are-finitely-presented
---

Let `g ≥ 3` and `m = 6g − 7`.

- **Embedding.** `closed-mcg-embeds-in-rational-projective-full-group` embeds
  `L = Mod(S_g)` (all of it, since `g ≥ 3`) in `𝒯_m`.
- **Host hypotheses.** It also proves `𝒯_m` is full and clopen transitive on the
  Cantor space `Ŝ_m`.
- **Finite presentation.** `rational-projective-full-groups-are-finitely-presented`
  supplies the remaining hypothesis.

These are exactly the three hypotheses of
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, together with the
embedding required by `closed-mcg-virtually-embeds-in-fp-full-cantor-group`.
