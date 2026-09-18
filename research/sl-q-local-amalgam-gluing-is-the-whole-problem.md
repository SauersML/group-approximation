---
rg: 2
id: sl-q-local-amalgam-gluing-is-the-whole-problem
kind: claim
title: SL_m(Q) is the colimit of its four-index subgroups, so gluing hosts of the pieces of any such amalgam is equivalent to embedding SL_m(Q)
distinct_from:
  sl-n-q-is-colimit-of-lattice-stabilizers: that is the S-arithmetic (Bruhat--Tits, all primes) colimit of integral lattice stabilizers; this is the spherical colimit of the rational subgroups SL_I(Q), |I| <= 4, and it records that gluing them is the whole problem.
  gl-n-q-root-needs-only-nontrivial-psl-maps: that reduces the root to nontrivial homomorphisms of PSL_n(Q); this uses it to show that amalgam (BN-pair, Curtis--Tits, local Steinberg) presentations of SL_m(Q) give no further reduction.
  bh-embeddability-forces-decidable-edge-membership: that shows embeddability in finitely presented simple groups is not closed under HNN extensions and amalgams over finitely generated edges in general; this concerns one specific spherical amalgam with non-finitely-generated pieces.
artifacts:
  - research/artifacts/gq-gq-borel-q-amalgams.md
---

**ESTABLISHED** by `sl-q-local-amalgam-gluing-is-the-whole-problem-proof`
(elementary modulo Steinberg's presentation of `SL_m` over a field; not
independently reviewed; no novelty claimed). It records a **dead end**: amalgam
presentations of `SL_m(Q)` do not reduce the root.

## Statement

Let `m >= 3`. For `I ⊆ {1, ..., m}` let `SL_I(Q) <= SL_m(Q)` be the matrices that
preserve `span{e_i : i in I}`, fix every other `e_j`, and have determinant 1.
Let `𝒜_m` be the diagram of the groups `SL_I(Q)`, `2 <= |I| <= 4`, with the
inclusions `SL_J(Q) <= SL_I(Q)` for `J ⊆ I`.

1. **Colimit.** The colimit of `𝒜_m` is `SL_m(Q)`, via the inclusions.
2. **Gluing = homomorphisms.** For every group `S`, restriction is a bijection
   between homomorphisms `SL_m(Q) -> S` and compatible families
   `(φ_I : SL_I(Q) -> S)` over `𝒜_m`.
3. **Gluing = embedding (odd m).** For odd `m`, `SL_m(Q)` embeds in `S` iff `𝒜_m`
   has a compatible family into `S` that is nontrivial on some `SL_I(Q)`.

## Consequences for BN-pair and amalgam routes

- **No reduction.** "Embed the pieces, then glue the hosts" is exactly as hard as
  embedding `SL_m(Q)`: by (3), a single host carrying a compatible family *is* a
  host of `SL_m(Q)`. Separate hosts of the pieces give nothing. The same holds
  for the Curtis--Tits amalgam (simple-root subgroups of rank <= 2) and for Tits'
  amalgam of rank-2 parabolics whenever their universal completion is
  `SL_m(Q)`. Every piece with `|I| >= 3` contains `SL_3(Q) ⊇ SL_3(Z)`, so no
  amalgam of this kind reduces the root below `n = 3`.
- **No curvature shortcut.** In the rank-3 Curtis--Tits triangle for `m = 4`
  (vertex groups `SL_{123}`, `SL_{234}`, `SL_{12} x SL_{34}`; edge groups the
  three root `SL_2`s), diagonal elements of two different edge groups commute.
  So each vertex link has girth 4 and Gersten--Stallings angle `π/2`, in every
  host where the vertex groups embed; the angle sum is `3π/2 > π`. Nonpositive
  curvature developability criteria never apply to hosts of these pieces.
- **No general permanence to invoke.** Embeddability in finitely presented simple
  groups is not closed under amalgams in general
  (`bh-embeddability-forces-decidable-edge-membership` (ii)). The permanence
  obstructions of `mixed-permanence-closures-collapse-boone-higman-to-base` use a
  finitely generated FA probe, and `SL_m(Q)` is neither (it is countable and not
  finitely generated), so those results neither help nor forbid a gluing theorem
  here.

The Borel `B_m(Q)` and minimal parabolics do not help either: Tits' parabolic
amalgam needs rank-2 parabolics whose Levi factors contain `GL_3(Q)`; and for
`m = 3` the amalgam `P_1 *_B P_2` of the two minimal parabolics is not `GL_3(Q)`
(the building of `GL_3(Q)` is not a tree), so a host of it need not contain
`GL_3(Q)`. See the artifact for `B_m(Q)` itself.
