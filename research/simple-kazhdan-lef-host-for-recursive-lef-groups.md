---
rg: 2
id: simple-kazhdan-lef-host-for-recursive-lef-groups
kind: claim
title: One infinite finitely generated simple Kazhdan LEF group contains every recursively presented finitely generated LEF group
distinct_from:
  universal-simple-kazhdan-lef-groups-exist: that host is for recursively presented residually finite groups, through Wilson's theorem; this host is for recursively presented LEF groups, through a 2-generator LEF lemma, and it also contains non-residually-finite members such as G_Y with recursive language.
  simple-kazhdan-lef-host-for-countably-many-rf-groups: that is one host for a countable family of f.g. residually finite groups; this is one host for a countable family of countable LEF groups.
  simple-kazhdan-lef-hosts-all-countable-locally-finite: that is one host over Z for all countable locally finite groups; this is one host for all recursively presented f.g. LEF groups, built over a lamplighter action.
artifacts:
  - research/artifacts/sk-universal-lef-host-b-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Route: `simple-kazhdan-lef-host-for-recursive-lef-groups-proof`.

(a) For every countable set `𝒞` of countable LEF groups, one infinite, finitely generated, simple Kazhdan LEF group
`U` contains a copy of every member of `𝒞`.

(b) One such `U` contains every recursively presented finitely generated LEF group. These include:
- every finitely presented residually finite group;
- every finitely generated linear group over a field (residually finite by Malcev; recursively presented as in
  `universal-simple-kazhdan-lef-groups-exist-proof`);
- every `G_Y = EL_3(LC(Y,F_2)⋊Z)` for an infinite minimal subshift `Y` whose language is recursive, since its word
  problem has the degree of the language (`subshift-elementary-group-word-problem-degree`). Examples: the Fibonacci
  subshift, and Sturmian subshifts of computable slope. Which of these are pairwise non-isomorphic is not claimed;
- every derived topological full group of a minimal subshift with recursive language (Matui; Grigorchuk–Medynets).

**Sharpness.** No countable group contains every finitely generated LEF group
(`no-countable-group-contains-all-fg-lef-groups`). So (b) needs its countability restriction.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS (§3). Note N6: the linear-group example relies on solvable word problem for f.g. linear groups (Rabin, Malcev), which is recalled and not re-read.
