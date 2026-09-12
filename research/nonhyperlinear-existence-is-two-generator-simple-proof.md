---
rg: 2
id: nonhyperlinear-existence-is-two-generator-simple-proof
kind: route
title: Localize a counterexample, take Schupp's simple envelope, and compactify one word
target: nonhyperlinear-existence-is-two-generator-simple
requires:
  - local-approximation-properties-are-marked-closed
  - countable-group-embeds-in-two-generator-simple-group
  - hyperlinear-radical-presentation-compactness
---

Assume a countable nonhyperlinear group `G` exists.  Hyperlinearity is local
by `local-approximation-properties-are-marked-closed`, so some finitely
generated subgroup `H<=G` is nonhyperlinear.  Apply Schupp's theorem to embed
the countable group `H` in a two-generator nonabelian simple group `S`.

If `S` were hyperlinear, subgroup heredity from the same local-approximation
theorem would make `H` hyperlinear.  Hence `S` is nonhyperlinear.  This proves
clause 1 implies clause 2; the reverse implication is immediate.

Write `S=<a,b | R>`.  The free group `F(a,b)` is countable, so its normal
subgroup `R` has some enumeration `r_1,r_2,...`.  Fix any word `w` with
nontrivial image in `S`.  Every homomorphism from `S` to a tracial matrix
ultraproduct is trivial: a nontrivial such homomorphism has proper normal
kernel, and simplicity would make that kernel trivial, giving a hyperlinear
embedding of `S`.  Therefore `w` lies in the hyperlinear radical of `S`.

Apply `hyperlinear-radical-presentation-compactness` to this enumeration.
It gives exactly `(TGS1)` for every `epsilon>0`, proving clause 3.
Conversely, `(TGS1)` and the same compactness theorem put the nontrivial word
`w` in the hyperlinear radical, which rules out a hyperlinear embedding of
`S`.  Thus clause 3 implies clause 2 and all three clauses are equivalent.
