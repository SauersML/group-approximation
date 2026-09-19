---
rg: 2
id: finite-conjunction-rstar-cap-firewall-proof
kind: route
title: Push the unavoidable magic-AND support through the cap-range sandwich
target: rstar-cap-selection-unstable-under-matrix-conj
requires:
  - matrix-conj-forces-unsafe-support
  - fano-cap-witness-sections-force-source-affine-safety
  - culf-mastel-rstar-fixed-language-gap-is-published
---

Every trace on the lifted instance restricts to the unique trace of the
magic-AND block, hence all four AND graph atoms remain positive.  Select one
positive target witness below each atom.  If all target occurrence supports
were Fano caps, the established witness-section sandwich would put the
affine hull of the four atoms inside the AND relation.  Their odd xor is the
forbidden atom `110`, a contradiction.
