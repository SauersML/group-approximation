---
rg: 2
id: fp-simple-group-not-coarsely-embeddable-in-hilbert-space
kind: claim
title: Some finitely presented simple group does not coarsely embed into Hilbert space, and so fails the Baum--Connes conjecture with coefficients
distinct_from:
  fp-simple-nonexact-group: that asks for a finitely presented simple group without property A; this asks for the strictly stronger failure of coarse embeddability, which implies non-exactness, and it brings a failure of Baum--Connes with coefficients with it.
  baum-connes-counterexample-group-exists: that asks for a failure with trivial coefficients in any countable group, and is a different and harder question; this asks only for coefficients, but in a finitely presented simple group.
---

**OPEN.** There is a finitely presented simple group `S` whose Cayley graph does not
coarsely embed into Hilbert space. Then `S` also fails the Baum--Connes conjecture with
coefficients, as explained below.

## Why the two failures come together

Suppose `S` contains a finitely generated subgroup `G` whose Cayley graph contains an
isometrically embedded expander. Then:
- **No coarse embedding.** Expanders do not coarsely embed into Hilbert space, and a
  finitely generated subgroup is coarsely embedded in `S`. So `S` does not coarsely embed
  either.
- **Baum--Connes with coefficients fails for `G`.** Osajda, arXiv:1406.5015, Corollary
  `c:Hilbert` (read at source) states this, via Higson--Lafforgue--Skandalis §7.
- **The failure passes up to `S`.** Baum--Connes with coefficients passes to subgroups
  (Chabert--Echterhoff, permanence; cited, not re-read). So if `S` satisfied it, `G`
  would too.

## Routes

- **Through Boone--Higman for one decidable input.** By
  `decidable-graphical-non-exact-groups-exist` item 1, `G_exp` is finitely generated,
  has solvable word problem, and contains isometric expanders. Boone--Higman, or even its
  graphical case `graphical-small-cancellation-inputs-satisfy-boone-higman`, puts `G_exp`
  in a finitely presented simple `S`, and the argument above applies. The route is
  `fp-simple-non-coarsely-embeddable-group-via-graphical-bh`.
- **Hosts excluded.** No Haagerup group qualifies as `S`, since Haagerup groups coarsely
  embed. So `F`, `T`, `V`, the Higman--Thompson groups and SFT full groups are out.
  Whether `nV` qualifies is open: its a-T-menability is OPEN
  (`brin-thompson-groups-nv-are-a-t-menable`). The only finitely presented simple host in
  the graph known not to be Haagerup is `L^x`.

## Known finitely presented examples that are not simple

Sapir's closed aspherical manifold groups coarsely contain expanders (Osajda, Corollary
`c:Sapir`). So there are finitely presented groups that are not coarsely embeddable. None
is known here to be simple, or to embed in a finitely presented simple group.
