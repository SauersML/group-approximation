---
rg: 2
id: cm-empty-replacement-fano-section-proof
kind: route
title: Cap-complete every final two-visible R-star commutativity row
target: cm-empty-replacement-is-fano-cap-safe
requires:
  - rstar-two-retained-coordinates-admit-a-fixed-cap-section
  - culf-mastel-rstar-fixed-language-gap-is-published
---

Read Proposition 6.2 and the proof of Part 1 of Culf--Mastel Theorem 4.14:
the final non-TVF step replaces each arity-two empty constraint by one target
row retaining exactly its two old variables, with all other variables fresh.
Apply the established two-retained-coordinate section into one maximal Fano
cap to the joint PVM of those old variables.  Freshness makes the extensions
simultaneous, and the formulas use only spectral sums in the original finite
tracial algebra.  Restriction gives the converse.
