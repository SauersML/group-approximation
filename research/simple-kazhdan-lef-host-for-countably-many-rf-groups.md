---
rg: 2
id: simple-kazhdan-lef-host-for-countably-many-rf-groups
kind: claim
title: One infinite f.g. simple Kazhdan LEF group contains every group of a given countable family of f.g. residually finite groups
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that gives one envelope per group; this gives one envelope for a whole countable family, for example all finitely presented residually finite groups together with all finitely generated linear groups.
  simple-kazhdan-lef-hosts-all-countable-locally-finite: that is one host over Z for all countable locally finite groups; this is a host for countable families of f.g. residually finite groups, built over a residually finite overgroup.
artifacts:
  - research/artifacts/sk-strong-3-universal-host-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Theorem U.** For every countable set `F` of finitely generated residually finite groups there is an infinite,
finitely generated, simple group `S` with property (T) that is LEF, hence sofic and hyperlinear, and contains a copy of
every member of `F`.

**Corollary U′.** One such `S` contains:
- every finitely presented residually finite group;
- every finitely generated linear group over a field (Malcev, `finitely-generated-linear-groups-are-residually-finite`);
- every finitely generated residually finite group with solvable word problem. This includes the finitely presented
  ones, by `fp-residually-finite-groups-have-solvable-word-problem`.

In particular it contains `SL_n(Z)` for every `n`, every finitely generated subgroup of `GL_n(C)`, surface groups,
and every finite group.

**Countability of the example classes.** Each is countable up to isomorphism.
- Finitely presented groups: there are countably many finite presentations.
- Solvable word problem: the relators on a finite generating set form a recursive set, and there are countably many
  recursive sets.
- Linear groups:
  - finitely many matrices lie over the finitely generated field their entries generate;
  - finitely generated fields are countable, and so are their isomorphism types;
  - there are countably many tuples of matrices over each.

**Sharpness.** No finitely generated group contains every finitely generated residually finite group. A finitely
generated group has countably many finitely generated subgroups, and there are uncountably many finitely generated
residually finite groups up to isomorphism (Chong–Wise, arXiv:2207.00410, abstract). Every subgroup of `S` is LEF.

Route: `simple-kazhdan-lef-host-for-countably-many-rf-groups-proof`.
