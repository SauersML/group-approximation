---
rg: 2
id: torsion-freeness-pi2-proof
kind: route
title: A universal quantifier over a difference of two r.e. events, and the switch with a finite cyclic seed
target: torsion-freeness-recognition-is-pi2-complete
requires:
  - arbitrary-forbidden-seed-hereditary-property-switch
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
---

**Membership.**  Fix a recursive presentation.  The predicate
`T(w, n) := (w^n = 1 -> w = 1)` is the disjunction of the co-r.e. predicate
"`w^n != 1`" and the r.e. predicate "`w = 1`", hence `Delta^0_2` and in
particular `Pi^0_2`; torsion-freeness is `forall (w, n) T(w, n)`, and
`Pi^0_2` is closed under universal number quantification (merge the two
universal quantifiers by pairing).

**Hardness.**  Torsion-freeness is invariant under group isomorphism, holds
for the trivial group, and fails for `Z/2 = <a | a^2>`, a finite
presentation.  Apply
[[arbitrary-forbidden-seed-hereditary-property-switch]] with that seed:
`G(d, c) ~= 1` for `c in INF` and `~= Z/2` for `c in FIN`, so
`c |-> switchCode(d, c)` reduces `INF` to torsion-freeness of enumerated
presentation codes.  For two generators compose with the bridge
[[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]: `B2(1)`
embeds in `F_2 x F_2` and is therefore torsion-free, while `B2(Z/2)`
contains `Z/2`.  Since `INF` is `Pi^0_2`-complete, so is torsion-freeness;
complements give the `Sigma^0_2` statement.
