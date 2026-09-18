---
rg: 2
id: decidable-groups-lie-in-fp-topologically-free-crossed-products
kind: claim
title: Every decidable group lies in a finitely generated group with a minimal topologically free subshift, with torsion-free isotropy, whose binary crossed product is finitely presented
distinct_from:
  decidable-groups-lie-in-fp-free-minimal-crossed-products: that is premise (E), with a free action; this is the relaxed premise (E′), which asks only for topological freeness and freeness of finite subgroups, so (E) implies (E′).
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is P1 with free SFTs; (E′) allows boundary-type (compression) shifts, which exist over groups with many ends where free SFTs do not.
---

**OPEN.** Premise (E′) of `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`
(lane bh-g3-topfree, 2026-09-18).

## Statement

For every finitely generated group `G` with solvable word problem, there are:
- a finitely generated group `Λ >= G`;
- a finite alphabet `A` and a nonempty subshift `X ⊆ A^Λ`, on which `Λ` acts minimally and
  topologically freely, and every finite subgroup of `Λ` acts freely;

such that `LC(X, F_2) ⋊ Λ` is finitely presented as an `F_2`-algebra.

## Relations

- (E) implies (E′), since free actions are topologically free with trivial isotropy.
- **Sufficient condition.** A finitely presented `Λ >= G` carrying a quantum-rigid, minimal,
  topologically free SFT with torsion-free isotropy
  (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`).
- **Decidability is consumed.** Under that sufficient condition `Λ` has solvable word problem, by
  `rigid-topologically-free-sfts-force-solvable-word-problem`. So (E′) can only hold for
  decidable `G`, as it must.
- **Known instances.** Every finitely generated subgroup `G` of `F_m × F_n`, with `Λ = F_m × F_n` and
  `X = ∂T_m ⊠ ∂T_n` (`master-route-needs-only-topological-freeness`, item 4). Boone–Higman was already
  known for these groups.
- **Products with free groups add nothing.** For an overgroup of the form `Λ_0 × F_n`, a product shift
  has each required property iff its `Λ_0`-factor does (`master-route-needs-only-topological-freeness`).

## Where to look

What is new compared with (E) is compression-type codings, such as boundary shifts, over overgroups
with free-product or hyperbolic-like structure. They are quantum rigid by monotone chains of
projections rather than by determinism. Every free SFT over an infinitely-ended group is excluded
(Cohen, recalled), but topologically free boundary codings are not.

The open design problem is a boundary-type coding over an fp overgroup of an arbitrary decidable
`G` that stays of finite type. A Bass–Serre end orientation over a group with infinite vertex
stabilizers is not a local rule over the group, since each vertex sees infinitely many edges.
