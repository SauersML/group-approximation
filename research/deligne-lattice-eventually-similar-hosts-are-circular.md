---
rg: 2
id: deligne-lattice-eventually-similar-hosts-are-circular
kind: claim
title: Deligne's lattice embeds in an eventually similar host only if a vertex group already contains a non-residually-finite quotient-by-finite of a finite-index subgroup with infinite center
distinct_from:
  deligne-lattice-embeds-in-no-rover-nekrashevych-group: that excludes Rover--Nekrashevych hosts, whose vertex groups are residually finite; this covers every eventually similar host with an arbitrary groupoid and shows that the embedding problem reappears inside one vertex group.
  fw-nst-inputs-virtually-embed-in-one-vertex-group: that is the general transfer theorem for FW inputs with a normal subgroup dichotomy; this verifies the dichotomy for Deligne's lattice through Margulis's theorem and Deligne's failure of residual finiteness, and records what the vertex group must contain.
  deligne-lattice-satisfies-boone-higman: that is the OPEN embedding question; this is a reduction showing one host shape can only move the question into a vertex group.
artifacts:
  - research/artifacts/hl-bh-deligne-host-2026-09-13.md
---

**ESTABLISHED** through `deligne-eventually-similar-circularity-proof`
(not independently reviewed; no novelty claimed).

Let `n >= 2`, `p: Gamma~ -> Sp_2n(Z)` the preimage of `Sp_2n(Z)` in the
universal cover of `Sp_2n(R)`, and `z` a generator of `ker p`. Suppose
`Gamma~ <= G`, where `G` is eventually `H`-similar in the setting of
`fw-subgroups-of-eventually-similar-groups-virtually-embed`.

**Statement.** Some vertex group `H_s` contains a subgroup isomorphic to
`Q = L / F`, where:
- `L` has finite index in `Gamma~`;
- `F` is a finite normal subgroup of `L` with `F cap ker p = 1`.

`Q` has the same obstruction package as `Gamma~` itself:
1. `Q` is not residually finite;
2. the image of `ker p cap L` is central in `Q` and infinite cyclic, so `Q` has
   infinite center;
3. consequently `Q` carries no action of type (A)
   (`type-a-actors-have-no-infinite-virtually-central-subgroup`).

**Consequence for the host programme.** An eventually similar host gives no
reduction for `Gamma~`: it contains `Gamma~` only if one vertex group of its
groupoid, itself a group of homeomorphisms of a cone space, already contains a
copy of such a `Q`. This covers:
- Rover--Nekrashevych groups and the synchronous case, where the vertex groups
  are residually finite and no `Q` fits, recovering
  `deligne-lattice-embeds-in-no-rover-nekrashevych-group`;
- graph almost-automorphism groups and every eventually self-similar groupoid
  over a shift of finite type, including those with non-residually-finite
  vertex groups, the case left untested in the Attempts of
  `deligne-lattice-satisfies-boone-higman`.

**Scope.** Nothing is said about finite presentation of any host, about full
Cantor groups with finitely many singular points that are not eventually
similar (such as the shell envelopes of
`shell-cantor-embeddings-are-finite-germ-extensions`), or about Brin--Thompson
groups `nV`, where cone markings are not commensurated.
