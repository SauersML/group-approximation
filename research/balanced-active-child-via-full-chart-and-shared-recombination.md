---
rg: 2
id: balanced-active-child-via-full-chart-and-shared-recombination
kind: route
title: Return each finite child chart and recombine only its shared marginals
target: balanced-schur-active-child-is-next-prefix-source
requires:
  - translation-symmetrized-schur-child-reset
  - hnn-full-child-chart-transports-every-type-corner
  - shared-bcs-active-recombination-after-schur-returns
  - corner-localized-non-ce-bcs-energy-gap
---

The finite reset makes the corrected child types canonical, and the full
child HNN edge transports every joint type/prefix corner without performing
the forbidden factor-two conjugacy.  The recombination claim identifies the
returned one-variable marginals on one common next carrier.  The
corner-localized robust BCS gap then applies at the next level, while the
Schur branch balance shows that only one child copy was lost to the exit.

