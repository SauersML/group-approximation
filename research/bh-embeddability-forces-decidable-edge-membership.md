---
rg: 2
id: bh-embeddability-forces-decidable-edge-membership
kind: claim
title: An HNN extension or double over a finitely generated edge embeds in a finitely presented simple group only if edge membership is decidable
distinct_from:
  compilers-cannot-drop-the-decidability-hypothesis: that forces the INPUTS of two proposed Boone-Higman compilers to have solvable word problem; this forces the EDGE subgroups of HNN and amalgam steps to have decidable membership, and shows that embeddability into finitely presented simple groups is not closed under those steps.
  simple-envelope-forces-solvable-word-problem: that is decidability of the word problem for subgroups of a finitely presented simple group, and is an input here; this is the membership consequence for the edge subgroup of an HNN extension or double, together with an explicit non-closure example.
---

**(i)** Let `A` be finitely generated and `C <= A` finitely generated. If the
HNN extension `A*_C = <A, t | t c t^-1 = c (c in C)>` or the double
`A *_C A` embeds in a finitely presented simple group, then `A` has solvable
word problem and membership in `C` is decidable in `A`.

**(ii)** Embeddability into finitely presented simple groups is closed neither
under HNN extensions nor under amalgamated free products over finitely
generated subgroups. Explicitly, there are a torsion-free hyperbolic group `G`
and a two-generated normal subgroup `N <| G` such that `G` embeds in a finitely
presented simple group while neither `G*_N` nor `G *_N G` does.

## Where decidability must enter a Higman-type upgrade

Higman-type envelopes are built by HNN extensions and amalgamations. By (i),
any step-by-step upgrade of such a construction to finitely presented simple
envelopes needs decidable edge membership at every step, and (ii) shows that
this hypothesis cannot be dropped. Conversely, decidable membership in both
associated subgroups together with a computable edge isomorphism is exactly
what Britton's reduction consumes to keep the word problem solvable through an
HNN step. The permanence statement with that hypothesis is the open claim
`bh-embeddability-survives-decidable-edge-hnn`.
