---
rg: 2
id: fg-simple-hyperlinear-tree-group-not-finitely-presented
kind: claim
title: Amenable-edge tree splittings already give finitely generated simple hyperlinear groups, but Le Boudec's are not finitely presented
distinct_from:
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: That is the permanence theorem for finite graphs of hyperlinear groups over amenable edges; this applies it to Le Boudec's simple groups acting on trees, and identifies finite presentation as the property they lack.
  hyperlinear-fp-infinite-simple-group: That is the open root asking for a finitely presented example; this is the established finitely generated calibration showing where the live splitting route stops.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

**ESTABLISHED.**  Let `d >= 3` and let `F < F' <= Sym(d)` be permutation
groups with `F` semi-regular.  Let `G(F,F')` be Le Boudec's group of
automorphisms of the `d`-regular tree whose local action lies in `F'`
everywhere and in `F` at all but finitely many vertices, and let
`G(F,F')^*` be its bipartition-preserving subgroup of index two.  Then:

1. `G(F,F')` is finitely generated and its vertex stabilizers are infinite
   locally finite groups.
2. For suitable `(F,F')`, `G(F,F')^*` is an infinite simple group.
3. `G(F,F')` and `G(F,F')^*` are hyperlinear, because they are fundamental
   groups of graphs of locally finite groups.
4. Neither is finitely presented, because both are quasi-isometric to the
   lamplighter `C_n wr W_d` over the infinite virtually free group
   `W_d = C_2 * ... * C_2`.

So the amenable-edge splitting route of `hyperlinear-fp-infinite-simple-group`
does produce finitely generated infinite simple hyperlinear groups.  Its only
known examples lose finite presentation through locally finite, hence not
finitely generated, stabilizers.  A finitely presented example needs finitely
generated amenable edge groups.

Proof: `fg-simple-hyperlinear-tree-group-proof`.
