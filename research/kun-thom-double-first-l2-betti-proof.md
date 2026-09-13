---
rg: 2
id: kun-thom-double-first-l2-betti-proof
kind: route
title: Fixed price one and Gaboriau's inequality β_1^(2) <= C - 1
target: kun-thom-double-has-vanishing-first-l2-betti-number
requires: [kun-thom-wreath-and-double-have-fixed-price-one, fpbs-amen2-betti-cost-input]
---

- The double `D = G *_Γ G` is infinite and has fixed price one
  (`kun-thom-wreath-and-double-have-fixed-price-one`), so some free p.m.p. action has cost one.
- Gaboriau's inequality `β_1^(2)(D) <= C(D) - 1` (`fpbs-amen2-betti-cost-input`) gives
  `β_1^(2)(D) <= 0`.
- L²-Betti numbers are nonnegative, so `β_1^(2)(D) = 0`.
