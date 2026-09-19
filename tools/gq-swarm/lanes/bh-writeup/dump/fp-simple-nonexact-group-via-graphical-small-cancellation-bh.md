---
rg: 2
id: fp-simple-nonexact-group-via-graphical-small-cancellation-bh
kind: route
title: Embed Osajda's decidable non-exact graphical group in a finitely presented simple group, using Boone--Higman only for graphical small cancellation inputs
target: fp-simple-nonexact-group
requires: [graphical-small-cancellation-inputs-satisfy-boone-higman, decidable-residually-finite-non-exact-group-exists, exact-groups-are-closed-under-extensions]
---

1. By `decidable-residually-finite-non-exact-group-exists`, Osajda's group `G`, built
   from a recursive input sequence, is finitely generated, non-exact, has solvable word
   problem, and is given by a graphical small cancellation presentation whose graph has
   finite components.
2. By `graphical-small-cancellation-inputs-satisfy-boone-higman` (OPEN), `G ≤ K` for some
   finitely presented simple group `K`.
3. Subgroups of exact groups are exact (`exact-groups-are-closed-under-extensions`). So
   `K` is not exact. `∎`

Compared with `fp-simple-nonexact-group-via-boone-higman`, this route needs Boone--Higman
only for one geometric family, not for all decidable inputs.

**Scope check needed.** Osajda's condition is graphical `C'(1/6)` on the components used
in 1703.03791. The claim is stated for `Gr'(1/6)`. Its implication `C'(1/6) ⇒ Gr'(1/6)`
for graphs with finite components is standard (Gruber), and was not re-read at source.
