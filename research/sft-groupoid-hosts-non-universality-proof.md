---
rg: 2
id: sft-groupoid-hosts-non-universality-proof
kind: route
title: Apply the complexity wall to the single-exponential bound, and a-T-menability to Kazhdan inputs
target: input-encoded-sft-groupoid-hosts-are-not-universal
requires:
  - complexity-bounded-host-classes-are-not-universal
  - sft-topological-full-groups-have-exponential-word-problem
  - sft-topological-full-groups-have-the-haagerup-property
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
artifacts:
  - research/artifacts/hl-bh-groupoid-embedding-2026-09-13.md
---

## Part 1

Let `K_fg` be the class of finitely generated subgroups of the groups
`[[G|Y]]`, over all one-sided irreducible shifts of finite type without isolated
points and all clopen `Y`. By `sft-topological-full-groups-have-exponential-word-problem`,
each member has, for some finite generating set, a word-problem algorithm
running in time `C*2^(C*l)`. This has the form `C_S*T(C_S*l) + C_S*l + C_S`
with `T(l) = 2^l`.

`complexity-bounded-host-classes-are-not-universal` then gives a two-generated
group `H` with solvable word problem embedding in no member of `K_fg`. If `H`
embedded in some `[[G|Y]]`, its image would be a finitely generated subgroup,
hence a member of `K_fg`. So `H` embeds in no member of `K`. The constants
`C_S` may depend on the graph, so no choice of graph depending on the input
helps.

## Part 2

Every `[[G|Y]]` embeds in `[[G]]` by extending with the identity off `Y`, and
`[[G]]` has the Haagerup property by
`sft-topological-full-groups-have-the-haagerup-property`. So every member of `K`
has it, and a countable Kazhdan subgroup is finite by the standard facts
recorded there. Deligne's lattice is infinite and Kazhdan
(`deligne-universal-cover-lattice-is-non-rf-kazhdan`), so it embeds in no member
of `K`.

## The idea log and the remaining shape

Idea 1 of `research/artifacts/ideas-boone-higman-2026-09-13.md` asks for a
Cuntz--Krieger or shift-of-finite-type groupoid built from the input, with the
input embedded in `D([[G_E]])`. Every such group is a member of `K`, so parts 1
and 2 apply. The requirements in "What a groupoid host must do instead" in the
target claim restate the hypotheses each part uses, together with the existing
eventually-similar circularity nodes.
