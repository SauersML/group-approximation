---
rg: 2
id: braid-no-haagerup-via-burger-pair
kind: route
title: "Dead: a Burger pair Z^2 x| Gamma inside a braid group would kill the Haagerup property"
target: some-braid-group-lacks-the-haagerup-property
requires:
  - braid-group-contains-z2-by-nonamenable-sl2z-subgroup
---

Dead. Its prerequisite is refuted (`braid-abelian-normalizer-actions-are-virtually-solvable`, which also
invalidates this route).

The intended implication: for `Γ ≤ SL_2(Z)` non-amenable acting naturally on `Z^2`, the pair
`(Z^2 ⋊ Γ, Z^2)` has relative property (T). Burger proved this for `Γ = SL_2(Z)` (*Kazhdan constants for
SL(3,Z)*, J. reine angew. Math. 413 (1991)); the extension to non-amenable subgroups is the standard one and was
not re-verified here. Relative property (T) for an infinite subgroup forces every conditionally negative
definite function to be bounded on it, so the Haagerup property would fail. The premise is stated for a subgroup
`A Γ` that need not split as a semidirect product; that the spectral argument on the dual torus still applies
there is expected but was not re-verified. The route is dead either way.
