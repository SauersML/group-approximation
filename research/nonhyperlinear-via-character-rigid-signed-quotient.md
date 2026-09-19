---
rg: 2
id: nonhyperlinear-via-character-rigid-signed-quotient
kind: route
title: Promote a non-CE BCS quotient through uniqueness of a signed-corner trace
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - unique-trace-signed-corner-quotient-forces-nonhyperlinear
  - character-rigid-signed-bcs-quotient
---

Choose a finite **monotracial** BCS algebra whose unique trace is not
Connes-embeddable, and realize it as the quotient of the character-rigid
signed corner.  Sector character rigidity and the absence of the selected
finite type from finite-dimensional representations make the normalized
canonical corner trace unique.  Pulling the BCS trace back through the
surjection therefore identifies its GNS von Neumann algebra with the
canonical signed corner.  Hyperlinearity of the group would make that corner,
and hence the BCS trace, Connes embeddable, a contradiction.

The monotracial source is forced by the proposed quotient: a unital quotient
of a unique-trace C-star algebra has at most one tracial state.  It is not
provided merely by `mipstar-bcs-tracial-nonru-exists`, which supplies
existence and non-embeddability of traces but no uniqueness theorem.
