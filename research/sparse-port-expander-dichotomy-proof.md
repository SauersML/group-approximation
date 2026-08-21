---
rg: 2
id: sparse-port-expander-dichotomy-proof
kind: route
title: Combine the one-over-density Poincare loss with expander ball packing
target: sparse-ports-either-lose-soundness-or-repeat-relative-pieces
requires:
  - finite-offset-pauli-rectangles-violate-relative-gr-sixth
---

For `(SP1)`, bound a port average by `alpha^-1` times the corresponding
uniform vertex average and apply the expander Poincare inequality.  To see
sharpness, assign one reflection to all dummy vertices and a macroscopically
different reflection to all ports.  At most `Delta|Q|` edges cross the
changed set, so the uniformly sampled equality-edge rejection is
`O(|Q|/|V|)`.

For the dense-port branch, a bounded-degree graph with fixed Cheeger (hence
spectral) expansion has uniform ball growth until a ball occupies half the
vertices.  Choose `R` so that an `R`-ball has more than `1/alpha_0` vertices
unless it already occupies half the graph.  If all ports were farther than
`2R+1`, their disjoint `R`-balls would contain more than `|V|` vertices.
Thus two ports have uniformly bounded distance.

There are finitely many oriented `D`-words of that length and finitely many
pair labels.  Pigeonhole across infinitely many nonisomorphic game
components yields the repeated relative two-syllable pattern.  The complete
pair table closes each occurrence into a Pauli rectangle, so the cited
relative-piece obstruction applies.

