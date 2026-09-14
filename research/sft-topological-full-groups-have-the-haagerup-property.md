---
rg: 2
id: sft-topological-full-groups-have-the-haagerup-property
kind: claim
title: Topological full groups of one-sided irreducible shifts of finite type have the Haagerup property, so their Kazhdan subgroups are finite
distinct_from:
  thompson-v-has-haagerup-property: that imports Farley's proper action for Thompson's group V alone; this imports Matui's zipper-action theorem for the topological full group of every one-sided irreducible shift of finite type, which contains V and the Higman--Thompson groups as special cases.
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that proves finiteness of FW subgroups for groups acting by canonical similarities on graphs whose vertices all have out-degree at least two, through a commensurated set; this imports a-T-menability for every irreducible shift of finite type, with no out-degree hypothesis, through a zipper action.
artifacts:
  - research/artifacts/hl-bh-groupoid-embedding-2026-09-13.md
---

**ESTABLISHED by citation** (`matui-sft-full-group-haagerup-citation`).

Let `(X, sigma)` be a one-sided irreducible shift of finite type and `G` its
etale groupoid, as in Matui, *Topological full groups of one-sided shifts of
finite type* (arXiv:1210.5800, Section 6.1). Then the topological full group
`[[G]]` has the Haagerup property.

Two standard facts turn this into the form used downstream (Cherix, Cowling,
Jolissaint, Julg and Valette, *Groups with the Haagerup property*, Progress in
Mathematics 197, Birkhauser 2001; the same source as
`thompson-v-has-haagerup-property`):

- the Haagerup property passes to subgroups;
- a countable group with both property (T) and the Haagerup property is finite.

## Consequences

- Every subgroup of `[[G]]` has the Haagerup property. This includes the
  commutator subgroup `D([[G]])`, which Matui shows is simple when `G` is purely
  infinite and minimal, and the groups `[[G|Y]]` for clopen `Y`, which embed in
  `[[G]]` by extending with the identity off `Y`.
- Every Kazhdan subgroup of `[[G]]` is finite. In particular Deligne's lattice
  (`deligne-universal-cover-lattice-is-non-rf-kazhdan`) embeds in no such group.
