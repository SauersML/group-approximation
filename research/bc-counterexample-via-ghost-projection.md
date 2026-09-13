---
rg: 2
id: bc-counterexample-via-ghost-projection
kind: route
title: Dead - refute trivial-coefficient Baum--Connes with the ghost projection of an expander in a Gromov monster
target: baum-connes-counterexample-group-exists
requires: []
---

**Dead.**

**The proposal.**
- Let `G` be a Gromov monster, whose Cayley graph contains a **weakly** embedded
  expander `X = ⊔ X_n`, or one of Osajda's isometric-expander groups, where the
  embedding is isometric.
  - Corrected 2026-09-13. An earlier version also listed Osajda's residually
    finite non-exact groups and called the embedding coarse.
  - Their relators are Z/2-homology covers and never form an expander family
    (`osajda-rf-relator-covers-are-not-expanders`).
- The spectral projection onto the functions that are constant on each `X_n`
  is a non-compact ghost.
- Higson--Lafforgue--Skandalis (GAFA 12 (2002); context, not imported) use it
  to show that reduced crossed products by `G` are not K-exact. So Baum--Connes
  with some commutative coefficients fails.
- The proposal is to read the same projection as a class in `K_0(C*_r G)`
  outside the image of assembly.

**Why it dies.** By `reduced-group-algebras-contain-no-nonzero-ghosts`,
`M_n(C*_r G)` contains no nonzero ghost. The ghost projection needs the
multiplication operators by indicator functions of the `X_n`, and those are
coefficients, not group elements. With trivial coefficients no short exact
sequence exists whose middle-term exactness the projection could violate.

**What survives.** The coefficient failure can still be transported to a group
algebra through a group whose reduced C*-algebra is a crossed product by `G`,
for example `V ⋊ G` for a countable `Z[G]`-module `V`. That is a different route.
