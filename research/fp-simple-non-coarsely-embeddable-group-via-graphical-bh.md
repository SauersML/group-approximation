---
rg: 2
id: fp-simple-non-coarsely-embeddable-group-via-graphical-bh
kind: route
title: Put the decidable graphical group with isometric expanders into a finitely presented simple group and pass the expander up
target: fp-simple-group-not-coarsely-embeddable-in-hilbert-space
requires: [graphical-small-cancellation-inputs-satisfy-boone-higman, decidable-graphical-non-exact-groups-exist]
---

1. By item 1 of `decidable-graphical-non-exact-groups-exist`, `G_exp` is finitely
   generated, has solvable word problem, is given by a graphical `C'(1/24)` presentation
   with finite components, and has an expander family isometrically embedded in its
   Cayley graph.
2. By `graphical-small-cancellation-inputs-satisfy-boone-higman` (OPEN), `G_exp ≤ S` for
   some finitely presented simple group `S`.
3. Inclusions of finitely generated subgroups are coarse embeddings for word metrics. So
   the expander family coarsely embeds in `S`, and `S` does not coarsely embed into
   Hilbert space. Baum--Connes with coefficients fails for `S` by the permanence argument
   in the target node. `∎`

`boone-higman-conjecture` implies step 2 directly, so it also implies the target.
