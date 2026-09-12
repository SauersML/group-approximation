---
rg: 2
id: el3-z-t-embeds-in-no-host-with-number-field-local-groups
kind: claim
title: EL_n of a ring with infinite-rank additive group embeds in no eventually similar Cantor group whose local vertex groups are linear over a number field
distinct_from:
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that virtually embeds FW subgroups in products of local vertex groups; this adds that for EL_n of an infinite-rank ring those products can never be linear over Qbar, so every such host is excluded for the transcendental Boone--Higman inputs.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that makes Kazhdan subgroups of V_d(H) virtually embed in H^n; this rules out every V_d(H) with H linear over Qbar as a host for EL_3(Z[t]) and its finite-index subgroups.
  char-zero-algebra-unit-hosts-exclude-unipotents: that excludes algebraic unit-group hosts in characteristic zero; this excludes homeomorphism hosts whose local maps are canonical similarities or come from groups linear over a number field.
artifacts:
  - research/artifacts/bh-full-cantor-ca-host-2026-09-12.md
---

**ESTABLISHED.** Let `R` be an associative ring that is finitely generated as a
ring, with `R ⊗ Q` infinite-dimensional over `Q`, and let `n >= 3`. Let `Lambda`
be a finite-index subgroup of `EL_n(R)`. For example, `R = Z[t]` and
`Lambda = SL_3(Z[t])`.

1. **Eventually similar hosts.** Let `G <= Homeo(X)` be eventually `H`-similar
   on the path space `X` of a finite directed graph with all out-degrees at least
   two, in the setting of `fw-subgroups-of-eventually-similar-groups-virtually-embed`.
   If every vertex group `H_s` is isomorphic to a subgroup of some
   `GL_(N_s)(Qbar)`, then `Lambda` does not embed in `G`.
2. **Rover--Nekrashevych hosts.** If `H <= Aut(T_d)` is self-similar and
   isomorphic to a subgroup of `GL_N(Qbar)`, then `Lambda` does not embed in
   `V_d(H)` or `V_(d,r)(H)`.

The proof is the route `el3-z-t-no-number-field-local-host-proof`.

**Covered host families.**
- **Canonical similarities (`H` trivial).** The Thompson groups of shifts of
  finite type:
  - the Higman--Thompson groups `V_(d,r)`;
  - the topological full groups of one-sided SFT groupoids of finite graphs in
    which every vertex has out-degree at least two. Their elements replace
    prefixes, `u zeta -> v zeta` with `t(u) = t(v)`.

  Here claim 1 needs only part 2 of the cited theorem, since an infinite FW group
  cannot be finite.
- **Number-field self-similar groups.** `V_d(H)` for self-similar `H` linear over
  `Qbar`. These include Zaremsky's affine hosts `R_0^k x| GL_k(R_0)` over
  one-dimensional coordinate rings `R_0` of a number field, which carry his
  `GL_n(Q)` theorem.
- **Every eventually similar host with number-field local groups.** Whatever the
  graph of cone types and however asynchronous the local maps.

**Consequence for `char-zero-linear-groups-satisfy-boone-higman`.** A finitely
presented full Cantor group `D` containing standard `V` and `SL_3(Z[t])`, the
target of that root's surviving host type, cannot be eventually `H`-similar for
any eventually self-similar groupoid `H` whose vertex groups are linear over
`Qbar`. Either its local maps carry a group that is not linear over any number
field, in the transcendental parameter itself, or `D` is not eventually similar
on any shift of finite type. The linear cellular-automaton candidate on
`(Z_p^3)^Z` is not yet placed on either side:
- its natural cylinders form a product over infinitely many directions, not a
  cone tree;
- on deep rectangular cylinders its maps restrict to affine Laurent maps over
  `Z[t^(+-1)]`.

**Scope.** This does not exclude rational similarity groups, whose nuclear maps
need not be onto, nor Brin--Thompson groups `nV`, whose bricks are not cones of
one shift of finite type, nor twisted Brin--Thompson groups. It uses property
(T) of `EL_n(R)` only through FW.
