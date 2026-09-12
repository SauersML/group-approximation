---
rg: 2
id: countable-group-embeds-in-fg-simple-kazhdan-group-proof
kind: route
title: Hull small cancellation twice over a hyperbolic Kazhdan group, then a maximal normal quotient
target: countable-group-embeds-in-fg-simple-kazhdan-group
requires: [countable-group-embeds-in-two-generator-simple-group, torsion-free-hyperbolic-kazhdan-partner-exists, proper-normal-subgroups-miss-the-normally-generating-core]
artifacts:
  - research/artifacts/simple-kazhdan-hosts-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Section 1 of the artifact gives the complete proof.

External inputs cited in the body:
- Hull, arXiv:1308.4345v2: Theorem 7.1, Corollary 5.7, Lemmas 3.5, 5.5 and
  5.8, and Definition 1.4, quoted from the PDF;
- Osin, arXiv:1304.1246, Lemma 7.1: s-normal subgroups act non-elementarily;
- free factors are hyperbolically embedded (Dahmani--Guirardel--Osin);
- property (T) passes to quotients.

Step 1 makes `F_1 = gamma_1(H)` contain `C'`. Step 2 needs the normal closure
`D` of `C'` to be suitable:
- non-elementary, by Osin's lemma;
- no finite subgroup normalized by `D`, because the maximal finite subgroup
  `D` normalizes is normal, and `K(F_1) = 1` by clause (d).

Step 3 uses that any `1 != s in C'` normally generates `Q`, and applies
`proper-normal-subgroups-miss-the-normally-generating-core`.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 18 of the
verification artifact). Lemma 5.8 needs `<h_1>` alone hyperbolically embedded,
which follows from the family statement. The trust surfaces are the quoted
statements listed above.
