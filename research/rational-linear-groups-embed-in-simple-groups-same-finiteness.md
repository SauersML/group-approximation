---
rg: 2
id: rational-linear-groups-embed-in-simple-groups-same-finiteness
kind: claim
title: Every finitely generated subgroup of GL_n(Q) embeds in a simple group with exactly the same finiteness properties (Llosa Isenrich–Schesler–Wu)
distinct_from:
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's theorem (arXiv:2405.09722, Theorem 1.2) giving finitely presented simple envelopes for finitely generated subgroups of GL_n(Q); this is Llosa Isenrich–Schesler–Wu's theorem giving simple envelopes with the input's own finiteness properties, which are infinitely presented when the input is.
  char-zero-linear-groups-satisfy-boone-higman: that embeds finitely generated linear groups of characteristic zero in finitely presented simple groups; this embeds finitely generated subgroups of GL_n(Q) in simple groups with the SAME finiteness properties as the input, including inputs that are not finitely presented.
  every-countable-group-embeds-in-a-simple-fp2-group: that is the universal FP_2 envelope question over all countable groups; this settles the linear-over-Q case with prescribed finiteness.
---

**ESTABLISHED (literature import)** by `lisw-theorem-1-4-citation`.

Let `H` be a finitely generated subgroup of `GL_n(Q)`. There is a simple group
`G` containing `H` such that `G` has the same finiteness properties as `H`
(type `F_m`, and type `FP_m(R)` for commutative rings `R ≠ 0`), and `G` admits
a quasi-retract onto `H`. The simple groups are Röver–Nekrashevych groups.

Consequences recorded by the same paper: for every `m` there is a simple group
of type `FP_m(Z)` that is neither finitely presented nor of type `FP_{m+1}(Z)`,
and there is a simple group of type `FP_∞(Z)` that is not finitely presented.

For Zaremsky Problem 1.25 this covers only linear inputs over `Q`, all of which
are recursively presented. The same paper prints Problem 1.25 as its Question
1.12, attributed to Zaremsky.
