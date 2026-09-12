---
rg: 2
id: thompson-v-marker-involution-is-formalizable
kind: claim
title: The marker involution along an infinite-order dihedral element of Thompson's V admits formalizing representatives
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that is the same marker rule over the integers, where it is not formalizable; this induces it to Thompson's V, where no landed obstruction applies and zero-divisor gates exist on one track.
  dihedral-marker-involution-is-formalizable: that is the same object over the infinite dihedral subgroup; a formalization there induces one here, but a refutation there does not pass up.
  binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable: that is the universal statement over finitely generated simple hosts; this is its first test object, and a refutation here refutes it.
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
---

**OPEN.** Let `a in F <= V` have infinite order, and define `g, s in V` by `g(0w) = 0 a(w)`,
`g(1w) = 1 a^(-1)(w)`, `s(0w) = 1w`, `s(1w) = 0w`. Then `<g, s>` is infinite dihedral. On `{0,1}^V` let
`tau_g` flip cell `h` exactly when
`(x(hg^(-3)), x(hg^(-2)), x(hg^(-1)), x(hg), x(hg^2), x(hg^3)) = (0, 0, 1, 1, 0, 0)`.
Then some polynomial representative `tau~` of `tau_g`, on a finite memory, satisfies `tau~ o tau~ = id`
formally. `tau_g` is its own unique left inverse.

`V <= L_(F_2)(1,2)^x`, so a formalization here induces one over the binary Leavitt unit group.

## Attempts

- **Encoder memory.** By `formal-pairs-push-along-quotients-of-the-encoder-memory-group`, every
  bi-orderable quotient of the encoder memory group kills `g`. The memory must leave `<g>`, and every
  subgroup that maps onto `Z` nontrivially on `g`. The dihedral subgroup `<g, s>` evades this.
- **No landed obstruction applies.** One-track affine rigidity needs a bi-orderable host
  (`finitely-generated-simple-groups-are-not-biorderable`). `V` has no proper finite-index subgroups.
  Pushforward is void once the memory generates `V`.
- **Gates exist on one track.** `V` carries non-affine one-track formal involutions
  (`non-central-involutions-carry-nonaffine-formal-involutions`). Whether words in zero-divisor shears and
  units of `F_2[V]` realize `tau_g` is open.
- **Smallest arena.** Over `<g, s>` the object is `tau_Z x tau_Z` over `Z` with reflection symmetry
  (`dihedral-marker-involution-is-formalizable`). Artifact Section 5.
