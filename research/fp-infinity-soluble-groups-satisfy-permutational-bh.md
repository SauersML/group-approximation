---
rg: 2
id: fp-infinity-soluble-groups-satisfy-permutational-bh
kind: claim
title: Soluble groups of type FP_∞ lie in the permutational Boone--Higman class modulo Kropholler's locally finite radical, and outright when that radical is finite (torsion-free, metanilpotent and constructible cases)
distinct_from:
  rf-soluble-minimax-groups-satisfy-permutational-bh: that assumes residual finiteness and finite Prüfer rank; this assumes only the homological finiteness condition FP_∞, and derives those hypotheses from Kropholler's structure theorem.
  fp-metabelian-groups-satisfy-boone-higman: that is finitely presented metabelian groups, of possibly infinite rank; this is soluble groups of any derived length under the stronger condition FP_∞.
  amenable-automatic-va-via-ea-and-soluble-case: that uses FP_∞ structure theory to reduce amenable automatic groups to the soluble case; this turns the same structure theory into Boone--Higman envelopes.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**ESTABLISHED** by `fp-infinity-soluble-groups-satisfy-permutational-bh-proof` (lane
`bh-solvable`, lane proof composing one literature import, read at source, with landed
nodes). Not independently reviewed. No priority is claimed: this is a direct corollary and
may be folklore.

## Statement

Let `G` be a soluble group of type `FP_∞` over `Z`, or finitely generated and of type
`FP_∞` over `Q`. By Kropholler's Theorem B, stated below, `G` has a locally finite normal
subgroup `T` with `G/T` constructible-by-finite.
- **(a)** `G/T` lies in `B_A`, so it embeds in a finitely presented simple group.
- **(b)** If `T` is finite, then `G` lies in `B_A`. This holds in particular in three cases:
  - `G` is torsion-free, since then `T = 1`;
  - `G` is metanilpotent, by Theorem C;
  - `G` is constructible-by-finite.

## Source (read at source)

P. H. Kropholler, *Soluble groups of type (FP)_∞ have finite torsion-free rank*, Bull.
London Math. Soc. 25 (1993) 558–566 (PDF via MSI institutional access, copy in
`gq/src/bh-solvable/`), p. 558–559:
- **Theorem B.** "Let `G` be a soluble group of type `(FP)_∞` over `Q`. Then `G` has
  finite torsion-free rank. More precisely, `G` has a locally finite normal subgroup `T`
  such that `G/T` is constructible-by-finite."
- **Definition used there.** A soluble group is constructible-by-finite if and only if it is
  a finite extension of a group built up from the trivial group by a finite sequence of
  ascending HNN-extensions.
- **Theorem C.** "Let `G` be a metanilpotent group. Then `G` is of type `(FP)_∞` over `Q`
  if and only if `G` is constructible-by-finite."
- **The open point.** The paper says: "Whether or not there exists a group `G` as in
  Theorem B where the subgroup `T` is infinite remains an open problem of some interest."
  So part (b) covers every soluble group of type `FP_∞` exactly when that problem has a
  negative answer.
