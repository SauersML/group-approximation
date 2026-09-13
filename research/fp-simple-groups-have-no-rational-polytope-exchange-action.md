---
rg: 2
id: fp-simple-groups-have-no-rational-polytope-exchange-action
kind: claim
title: A finitely presented infinite simple group has no nontrivial action by rational polytope exchanges of a torus, and none lies in the full group of a toral rotation coding through a rational polyhedral partition
distinct_from:
  fp-simple-groups-have-no-interval-exchange-action: that is the one-dimensional action statement; this covers tori of every dimension with integer facet normals, including rectangle exchanges, and adds the full groups of toral rotation codings
  circle-rotation-zd-derived-full-groups-are-not-fp: that shows derived and alternating full groups of free circle-rotation codings are not finitely presented, through finite type; this removes every finitely generated subgroup of the full group of a toral rotation coding through a rational polyhedral partition, through LEF
  labbe-shift-derived-full-group-is-finitely-presented: that asks whether one derived full group is finitely presented, for Labbé's partition with the irrational edge direction (1, -φ); this settles the question negatively only for partitions whose facet normals are integer vectors, which excludes Labbé's
---

**ESTABLISHED.** Notation is as in `rational-polytope-exchange-groups-are-lef`.

1. **Actions.** Let `S` be finitely presented, infinite and simple. Every homomorphism from
   `S` to the group of rational polytope exchanges of `T^k`, for any `k >= 1`, is trivial.
2. **Toral rotation codings.** Let `θ_1, ..., θ_d ∈ R^k` with `n·θ = Σ n_i θ_i ∉ Z^k` for
   every `n ∈ Z^d \ {0}`.
   - Let `f : [0, 1)^k -> A` be a finite coding whose fibres are rational polyhedral sets.
   - Put `c_z(n) = f({z + n·θ})`, and let `X ⊆ A^(Z^d)` be the closure of
     `{c_z : z ∈ [0, 1)^k}`.
   - Suppose `Z^d` acts freely on `X`.

   Then the topological full group `[[Z^d ~ X]]` embeds in the group of rational polytope
   exchanges of `T^k`. So no subgroup of `[[Z^d ~ X]]` is a finitely presented infinite simple
   group. In particular `D([[Z^d ~ X]])` and `A([[Z^d ~ X]])` are not finitely presented when
   they are infinite and simple, as they are for minimal `X`
   (`minimal-z2-subshift-derived-full-groups-are-fg-simple` for `d = 2`).

**Why it matters for `fp-infinite-simple-amenable-group`.**
- Rectangle exchanges and rational-slope polygon exchanges are the natural higher-dimensional
  analogues of the interval exchange groups, where amenability is known in rank two. None of
  them contains an example.
- A candidate built from a polyhedral toral rotation coding needs a facet normal that is not
  proportional to an integer vector. Labbé's partition has one, the edge direction `(1, -φ)`
  (`labbe-shift-is-a-toral-rotation-coding`, item 6). That is where the live candidate
  `fp-simple-amenable-via-labbe-shift-full-group` sits.

**Model test.** For `k = 1` and `d` generic rotations, statement 2 recovers the finite
presentation half of `circle-rotation-zd-derived-full-groups-are-not-fp` and extends it from
subgroups containing the rule 3-cycles to all finitely generated subgroups.

**Novelty.** None claimed. The recipe is the interval exchange one; see the Novelty paragraph
of `rational-polytope-exchange-groups-are-lef`.

Route: `fp-simple-groups-no-rational-polytope-exchange-proof`.
