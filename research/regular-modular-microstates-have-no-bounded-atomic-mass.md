---
rg: 2
id: regular-modular-microstates-have-no-bounded-atomic-mass
kind: claim
title: Regular modular microstates carry no positive mass on bounded-dimensional irreducibles
artifacts:
  - research/extremality-expels-bounded-dimensional-vertex-types.md
distinct_from:
  bounded-dimension-iwahori-pairs-have-holder-capture: that globally repairs tuples whose whole matrix dimension is bounded; this proves that even inside unbounded matrices the regular face has vanishing physical mass in every bounded irreducible-size window.
  bs14-character-split-leaves-only-the-regular-microstate-face: that selects the regular central character face of the arithmetic packet; this determines how the exact modular vertices must escape within that face.
  regular-iwahori-edge-types-have-moving-power-charge: that gives continuous finite-dimensional edge types after regular tensor camouflage; this proves a pure regular modular vertex cannot itself be assembled with positive density from any bounded-dimensional type family.
---

Let \(V=\operatorname{PSL}_2(\mathbb Z)\). Suppose exact representations
\[
 \sigma_n:V\longrightarrow U(d_n)
\]
have normalized characters converging pointwise to the regular character
\(\delta_e\).

Fix \(D<\infty\). Decompose \(\sigma_n\) into irreducibles and let
\(\sigma_n^{\leq D}\) be the direct sum, with multiplicity, of all irreducible
summands of dimension at most \(D\). Then
\[
 \frac{\dim\sigma_n^{\leq D}}{d_n}\longrightarrow0.       \tag{RAM1}
\]

Thus every regular-character countersequence furnished by
**capture-gap-localizes-to-regular-character-face** escapes through
irreducible modular types of unbounded dimension at both vertices. Repeating
a fixed noncongruence representation, mixing a compact family of
bounded-dimensional continuous types, or allowing arbitrarily large
multiplicities of such types cannot carry any positive fraction of the
regular corner.

The result is purely character-theoretic and uses no congruence
classification. It does not control unbounded irreducibles, their Iwahori
restrictions, or the relative position of the two vertex decompositions.
Those are exactly the remaining regular-face coupling variables, so the
nonhyperlinear-group root remains open.

DERIVATION
extremality-expels-bounded-dimensional-vertex-types
