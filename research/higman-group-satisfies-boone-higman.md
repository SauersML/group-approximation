---
rg: 2
id: higman-group-satisfies-boone-higman
kind: claim
title: Higman's four-generator group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that is the conjecture for every finitely generated group with solvable word problem; this is its test case at Higman's group, which is neither residually finite nor linear.
  baumslag-gersten-group-satisfies-boone-higman: that is the open case of the Baumslag--Gersten group; this is the open case of Higman's four-generator group.
  higman-group-embeds-in-no-almost-automorphism-group: that rules out every host inside an almost-automorphism group; this is the open embedding question itself.
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

**OPEN.** Let `H4 = < g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i ∈ Z/4 >`. The question is whether some finitely presented simple group contains `H4`.

**Known inputs.**
- **Word problem.** The word problem of Higman's group is decidable in polynomial time (Diekert--Laun--Ushakov, arXiv:1103.1232; abstract checked on 2026-09-13). So `H4` is a genuine Boone--Higman input.
- **No finite quotients.** `H4` has no nontrivial finite quotient (Higman 1951; recorded on main, §0 of `research/artifacts/higman-group-gottschalk-host-2026-09-12.md`).
- **BS(1,2) is forced.** Any nontrivial image of `H4` contains `BS(1,2)`. This is the hand lemma in approach 3 of `research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md`.
- **Geometry.** `H4` acts cocompactly on a CAT(0) square complex (Martin, arXiv:1506.02837; abstract-level only).
- **Not previously listed.** `H4` is not among the classes in BBMZ arXiv:2306.16356v3, Problem 5.3 (text read in the ideas artifact above).

## Attempts

- **Residually finite, linear and self-similar hosts: dead.**
  - Every finite image of `H4` is trivial, so `H4` embeds in no residually finite group.
  - Finitely generated linear groups are residually finite (Malcev), so no linear group contains `H4`.
  - A group acting faithfully on a locally finite rooted tree is residually finite: level stabilizers have finite index and intersect trivially. So no self-similar group contains `H4`.
- **Almost-automorphism hosts: dead.** By `higman-group-embeds-in-no-almost-automorphism-group`, every homomorphism from `H4` into any `A_(d,r)` is trivial. This rules out Higman--Thompson groups, Röver--Nekrashevych groups, and every finitely presented simple subgroup of them.
- **Not yet tested:**
  - Brin--Thompson groups `nV` with `n ≥ 2`;
  - rational similarity groups;
  - full groups of shifts of finite type with several cone types, or of non-amenable groupoids;
  - twisted Brin--Thompson envelopes over a finitely presented type (A) actor containing `H4`.

  Any host has to contain `BS(1,2)` and has to act on its Cantor space with at least one generator of `H4` not equicontinuous.
