---
rg: 2
id: delorme-guichardet-property-t-implies-fh
kind: claim
title: A topological group with property (T) has only bounded 1-cocycles, so its image under a continuous homomorphism to a Haagerup group is relatively compact
distinct_from:
  haagerup-cut-out-completions-force-haagerup-quotients: its proof lists Bekka-de la Harpe-Valette 2.12.4 as an unquoted standard input and concerns completions and quotients; this imports the Delorme-Guichardet theorem and the proper-cocycle definition verbatim, for continuous homomorphisms from any Kazhdan topological group.
  haagerup-t-exclusion: that excludes Haagerup carriers for (T)-compatible data in operator-algebraic settings; this is the plain group-level import that Kazhdan images in Haagerup topological groups are relatively compact.
---

**ESTABLISHED by citation** (`delorme-guichardet-property-t-implies-fh-citation`).

Let `H` be a topological group with property (T), let `G` be a topological
group, and let `b ∈ Z^1(G, π)` be a 1-cocycle for an orthogonal
representation `π` of `G` on a real Hilbert space.

1. (Delorme-Guichardet, BdlHV Theorem 2.12.4(i).) `H` has property (FH):
   every continuous affine isometric action of `H` on a real Hilbert space has
   a fixed point. Equivalently (BdlHV 2.2.9, 2.2.10) every 1-cocycle of `H` is
   bounded.
2. If `f : H → G` is a continuous homomorphism, then `b ∘ f` is a 1-cocycle of
   `H` for `π ∘ f`, so `b ∘ f` is bounded by item 1.
3. If `b` is proper (BdlHV: "for every bounded subset B of H, the set b^{-1}(B)
   is relatively compact in G"), then `f(H) ⊆ b^{-1}(B)` for a bounded ball `B`,
   so `f(H)` is relatively compact in `G`.

In particular, if `G` has the Haagerup property (BdlHV Definition 2.7.5), the
image of every continuous homomorphism from a Kazhdan group into `G` is
relatively compact. For a discrete Kazhdan group `H`, every homomorphism
`H → G` is continuous.

Items 2 and 3 are one-line consequences of the definitions, recorded in the
citation route with the quotes they rest on.
