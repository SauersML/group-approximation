---
rg: 2
id: nonhyperlinear-via-single-selected-atom-escape
kind: route
title: Grow a half-marked reducing carrier using one maximal forbidden atom at each level
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - single-selected-atom-hs-escape
  - single-selected-atom-escape-compiler
---

Use the fixed tracial/non-CE BCS, the one-bit selector menu, and the seed
Pauli pair.  The open escape cell supplies `(SAE1)` for whichever one of the
finitely many forbidden atoms is maximal on the current carrier.  The
conditional compiler then forces the marked central involution to disappear
in every normalized-HS approximation while its exact tracial model keeps it
equal to `-1`.

