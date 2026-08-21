---
rg: 2
id: stable-group-with-codense-kazhdan-subgroup
kind: claim
title: An HS-stable finitely generated group with an infinite-index finitely generated (T;FD) subgroup that is finite-dimensionally co-dense
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  hs-stable-finite-bi-index-kazhdan-pair-exists: that wants a stable ambient group with a finite-bi-index Kazhdan pair for site coherence; this wants an infinite-index Kazhdan subgroup whose fixed vectors in finite-dimensional representations are already fixed by the whole group, and the target group built from it is a Pauli wreath extension rather than a compiled atlas.
  dv-s-arithmetic-hs-stable-nonhyperlinear-extension: that needs stability of one S-arithmetic lattice with a central extension; this needs stability of a host with a co-dense Kazhdan subgroup, and the two stability targets are different groups.
---

Exhibit a finitely generated group `G`, HS-stable in the same-dimension
sense, and a finitely generated subgroup `G_0` with Lubotzky--Zimmer
property (T;FD), such that every finite-dimensional unitary representation
`pi` of `G` satisfies `pi^(G_0) = pi^G`.

By `pauli-lamplighter-over-stable-codense-kazhdan-pair` the Pauli
lamplighter `E_(G/G_0) x| G` is then an explicit nonhyperlinear group.
Sufficient for co-density: a 2-transitive action of `G` on the infinite set
`G/G_0` (`two-transitive-infinite-action-is-finite-dimensionally-codense`),
or strong approximation (`G_0` surjects onto every finite quotient of `G`
and all finite-dimensional representations factor through finite
quotients).

## Attempts

- **`SL_3(Z) <= SL_3(Z[1/p])`.**  Co-dense by strong approximation and
  superrigidity (finite-dimensional unitary representations of the
  S-arithmetic group factor through finite quotients, onto which `SL_3(Z)`
  already maps), and `SL_3(Z)` has (T).  Dies because `SL_3(Z[1/p])` is an
  infinite hyperlinear Kazhdan group, hence not HS-stable
  (`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`).  The host must
  not have (T).
- **Dogon--Vigdorovich's candidate `SL_2(Z[1/p])`.**  (T;FD) and
  conjecturally stable, but its finitely generated infinite-index subgroups
  act on Serre's tree: those fixing a vertex are virtually free and those
  acting without fixed points are not known to have (T;FD); none is known
  to be co-dense.
- **Free and virtually free hosts** (stable for trivial reasons).  Dies by
  M. Hall: finitely generated subgroups of free groups are profinitely
  closed, so a proper one is never co-dense; and no infinite (T;FD)
  subgroups exist.
- **Amenable hosts.**  Infinite residually finite amenable groups have no
  (T;FD) infinite subgroups (finite quotients give representations close
  to trivial without uniform gap).
- **Simple hosts** (André--Guirardel's finitely generated sharply
  2-transitive Kazhdan group, arXiv:2212.06020; Osin's groups with few
  conjugacy classes).  Co-density and the stabilizer condition are
  vacuous (no nontrivial finite-dimensional representations), but then
  stability of the host means every approximate representation is near
  the trivial one, which is already a strong form of nonhyperlinearity of
  the host itself; the lamplighter adds nothing for simple hosts.
- **Weakening to microstate stability does not help for residually finite
  hosts.**  The theorem only needs exact representations near the
  restrictions to `G` of canonical-trace microstates of the lamplighter,
  i.e. near approximate representations of `G` whose traces tend to the
  canonical trace.  But if `G` is residually finite and not HS-stable,
  tensoring a far-from-exact approximate representation `sigma_n` with a
  finite-quotient representation `rho_N` whose character tends to zero
  gives `rho_N (x) sigma_n`: defect and traces tend to zero while the
  restriction to the kernel of `rho_N` is `1 (x) sigma_n`, so for `N`
  growing slowly these stay far from exact.  Canonical-trace stability of
  a residually finite host is therefore genuine stability.
- **Consistency forcing.**  Stable and hyperlinear forces residually
  finite, so a host that is not already the witness is residually finite
  with a profinitely dense, finite-dimensionally co-dense, infinite-index
  finitely generated (T;FD) subgroup.  Known HS-stable groups are all
  "small" (finite, virtually abelian, free products of such, some
  amenable); the target is the first "large" stable group, which is the
  same bottleneck as every stability route, now without the central
  extension.
