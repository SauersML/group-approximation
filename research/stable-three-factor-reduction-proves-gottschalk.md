---
rg: 2
id: stable-three-factor-reduction-proves-gottschalk
kind: route
title: Stabilize arbitrary local rules and cancel long products by reversible shears
target: gottschalk-surjunctivity-conjecture
requires:
  - three-factor-finite-alphabet-ca-are-surjunctive
artifacts:
  - research/artifacts/gottschalk-stable-three-factor-reduction-2026-09-08.md
---

Identify a q-symbol alphabet with Z/qZ. Expand each local rule as
a finite sum of products of unary delta functions. For a term cAB
of factor length d>=4, split its factors into lengths at least two,
add fresh identity tracks u,v, and precompose by
(x,u,v)->(x,u+A(x),v+B(x)). Subtract c times the product of the two
new output tracks from the selected old output coordinate.

The selected term cancels. It is replaced by the terms -cuv, -cuB,
and -cvA, and the new outputs u+A and v+B. Every introduced term
has factor length less than d. The sum of 8^length over all output
term occurrences strictly decreases, including the newly added
identity terms. Thus finitely many steps give factor length at most
three. All changes are reversible local shears, and every added
track initially carries the identity map.

Consequently injectivity and surjectivity are preserved in both
directions. Apply the open prerequisite to the transformed injective
map and undo the changes. The one-symbol alphabet is immediate.
The proof of this implication is complete; its prerequisite remains
unproved and is not supplied by the reduction itself.
