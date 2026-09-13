---
rg: 2
id: grigorchuk-hnn-extension-has-only-finite-torsion-quotients
kind: claim
title: Every torsion quotient of Grigorchuk's finitely presented ascending HNN extension is finite
distinct_from:
  grigorchuk-ascending-hnn-extension-is-finitely-presented: that imports the finitely presented extension itself; this proves that none of its torsion quotients is infinite.
---

**ESTABLISHED** (proof in `grigorchuk-hnn-extension-has-only-finite-torsion-quotients-proof`).

Let `H = G*_phi` be Grigorchuk's finitely presented ascending HNN extension of the
first Grigorchuk group (`grigorchuk-ascending-hnn-extension-is-finitely-presented`).
Every torsion quotient of `H` is finite.

In particular, for every element `g` of `H` outside the normal closure `N` of `G`,
the finitely presented group `H / <<g>>` is torsion and finite. It is torsion
because its normal subgroup `N / (N ∩ <<g>>)` is torsion and has finite cyclic
quotient. So the torsion-by-cyclic route to Zaremsky Problem 1.11 is dead for
this group, for every choice of the killed element.
