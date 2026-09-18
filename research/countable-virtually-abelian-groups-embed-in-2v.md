---
rg: 2
id: countable-virtually-abelian-groups-embed-in-2v
kind: claim
title: Every countable virtually abelian group, in particular every countable abelian group, embeds in the Brin-Thompson group 2V
distinct_from:
  rationals-embed-in-brin-thompson-group-2v: that is Kojima--Sheng's copy of Q in 2V; this claim is the whole countable (virtually) abelian class, deduced from it.
  gl-n-q-embeds-in-fp-simple-group: that is the root; this claim settles only its virtually abelian pieces (Q^x, Q^n, tori, finite extensions) inside one finitely presented simple group.
artifacts:
  - research/artifacts/gq-bt-kojima-mechanism.md
---

**ESTABLISHED** through `countable-virtually-abelian-groups-embed-in-2v-proof`
(lane proof, not independently reviewed).

**Statement.** Every countable group with an abelian subgroup of finite index
is isomorphic to a subgroup of Brin's group `2V`, hence of `nV` for every
`n >= 2`.

**Consequences.**
- `2V` is finitely presented and simple (Brin; survey arXiv:2306.16356v3, §4,
  twisted Brin--Thompson subsection: "All of these groups are simple ... and
  finitely presented"). So `2V` is a second finitely presented simple group
  containing every countable abelian group. The first was Belk--Hyde--Matucci's
  `VA` (survey Theorem 4.11).
- For the root `gl-n-q-embeds-in-fp-simple-group`, `2V` contains `GL_1(Q)`,
  `Q^n`, the diagonal torus `(Q^x)^n`, and `Q^n ⋊ F` for every finite group
  `F` acting on `Q^n`. The non-abelian stepping stones need
  `rational-stepping-stones-in-nv-need-bs12-or-heisenberg`.

**Credit.** This is an immediate consequence of Kojima--Sheng's `Q <= 2V`
(arXiv:2603.18410v3, Theorem 1.2) together with Higman's embedding of
countable locally finite groups in `V`. No priority is claimed beyond
recording it. The novelty check was bounded: the Kojima--Sheng abstract and
theorem list, and a repository search, do not state it.
