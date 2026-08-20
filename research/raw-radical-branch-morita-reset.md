---
rg: 2
id: raw-radical-branch-morita-reset
kind: claim
title: Merge four transported radical branches into the next fixed-scale packet multiplicity
distinct_from:
  hnn-transports-forbidden-radical-atom-types: that preserves the four branch multiplicities separately; this must turn their sum into multiplicity of one next packet input.
  finite-graph-of-groups-representation-types-are-integer-flows: that supplies exact stationary flows defeating any purely Bass--Serre merge; this requires a genuine compressor, corner, or two-dimensional holonomy.
---

Starting from the four raw-word-labeled forbidden-atom branches transported by
`hnn-transports-forbidden-radical-atom-types`, construct a finite ordinary
group return cell such that:

1. the sum of their multiplicities becomes the multiplicity of one fresh
   baseline packet type of fixed irreducible dimension;
2. the normalized loss is at most `C sqrt(E)` and the relators used over all
   recurrent cells have bounded overlap;
3. complementary selector sectors either enter an explicitly tracked next
   type or pay ordinary relator energy; and
4. an exact infinite-dimensional marked model extends across the cell.

The cell cannot be a finite graph of finite groups: its regular representation
gives a stationary restriction flow. It must use a proper compressor corner,
a two-dimensional holonomy, or an equivalent non-Bass--Serre operation which
makes the four orthogonal branch carriers add rather than overlap.

## Attempts

- **Two HNN edges into one target:** fails because unitary intertwiners may
  reuse the same target subspace; they do not force orthogonal addition.
- **Make the next packet commute with the branch Pauli factor:** gives the
  desired tensor-factor formula locally, but literal iteration places future
  packets in all past commutants. A valid compressor must reset that history
  without reverting to stationary finite-group flow.
