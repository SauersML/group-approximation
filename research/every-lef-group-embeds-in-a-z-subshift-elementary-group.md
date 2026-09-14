---
rg: 2
id: every-lef-group-embeds-in-a-z-subshift-elementary-group
kind: claim
title: Every finitely generated LEF group is a subgroup of EL_3(LC(X,F_2)⋊Z) for some infinite minimal Z-subshift X
distinct_from:
  lef-groups-embed-in-simple-kazhdan-lef-groups: that allows any simple Kazhdan LEF envelope; this asks whether the note's own Z-family is universal.
refuted_by: [heisenberg-group-lies-in-no-z-subshift-elementary-group]
---

**REFUTED (unreviewed, sk-sl3z-bandwidth 2026-09-13).** The integer Heisenberg group is finitely generated and residually
finite, hence LEF, but it is a subgroup of no `GL_m(LC(X,F_q)⋊Z)`, hence of no `G_X`. The same holds for `SL_n(Z)`,
`n ≥ 3`. See `heisenberg-group-lies-in-no-z-subshift-elementary-group`.

Original question: is every finitely generated LEF group a subgroup of `G_X = EL_3(LC(X,F_2)⋊Z)` for some infinite
minimal Z-subshift `X`? A yes would have made the note's family universal for LEF groups.

## Attempts

- **Refutation by distortion (established, unreviewed).** `subshift-crossed-product-gl-has-no-distorted-elements`: in a
  finitely generated subgroup of `GL_m(LC(X,F_q)⋊Z)`, every infinite-order element has stable length `≥ 1/(2wm)`. Proof:
  Krylov dimension against propagation on the faithful orbit module. The Heisenberg centre has `|c^N| ≤ 12√N`, so the
  Heisenberg group, and `SL_n(Z) ⊇` it, lie in no `G_X`. Neither the banded representations nor dimension expansion are
  needed. Artifact: `research/artifacts/sk-sl3z-bandwidth-distortion-obstruction-2026-09-13.md`.

- **Reduction (established, unreviewed).** `z-family-lef-universality-reduces-to-gl-m-crossed-products`: it suffices
  to embed every f.g. LEF group in some `GL_m(LC(X,F_2)⋊Z)`.
- **Known members.** F.g. subgroups of `EL_n(F_2[t^{±1}])`, `n ≥ 3`, and of `[GL_m(F_2[t^{±1}]),GL_m(F_2[t^{±1}])]`
  (free groups, `SL_3(F_2[t^{±1}])`), every finite group, f.g. subgroups of `[[σ]]'`, and every `G_Y`
  (artifact part 1 §1).
- **Necessary conditions (established, unreviewed).** `fp-subgroups-of-subshift-gl-have-banded-representations`:
  - finitely presented members are residually finite and have w-banded F_2-representations injective on large balls;
  - every member has a faithful module with linear orbit-span growth.
- **Permutation encodings (die for expander-like quotients).** Expander Schreier graphs have linear bandwidth, so the
  permutation modules of such finite models are never banded with bounded width. Linear modules escape this: the natural
  module of `SL_n(F_2)` is banded while its Cayley graphs are expanders.
- **Conditional obstruction.** Take a finitely presented LEF group whose finite quotients' F_2-modules are uniform
  dimension expanders, with composition factors of unbounded dimension. It would be a subgroup of no `G_X`. The test
  object is `SL_3(Z)` (CSP, Kazhdan). No banded construction and no dimension-expansion theorem in characteristic 2 are
  known to this lane. See `research/artifacts/sk-lef-embedding-d-z-family-2026-09-13-part2.md` §5.
- **Lamplighter host.** sk-universal-embedding-b (22e2749154, unreviewed) uses `LC(2^Δ,F_2)⋊(Z/2≀Δ)`. Mapping its unit
  group into some `GL_m(LC(X,F_2)⋊Z)` would settle the question positively, and no such map is known.
