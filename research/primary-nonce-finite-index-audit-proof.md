---
rg: 2
id: primary-nonce-finite-index-audit-proof
kind: route
title: Compare each primary construction with the finite-index projective-core criterion
target: primary-nonce-sources-miss-finite-index-core
requires:
  - finite-index-projective-core-yields-central-witness
  - mipstar-does-not-supply-effective-projective-basis
  - cdi-native-envelope-inclusion-is-infinite-index
  - twisted-group-basis-forces-affine-context-support
---

The MIP-star abstract and construction give a game/correlation separation,
not a subfactor decomposition.  Paddock--Slofstra formulate the output as a
finitely presented BCS star algebra; their only linear-system bridge is
Proposition 5.8, which is already equivalent to the desired nonhyperlinear
group.  Hence neither source names the finite-index projective core required
by the criterion.

Manzoor's proof of the non-CE relation theorem displays the two inclusions
in `(PNS1)` and no index statement.  Definition 2.12 identifies the relation
algebra by adjoining `L^infinity(X)` to the IRS representation.  This is a
groupoid/relation construction and supplies no scalar projective basis.

Finally CDI Proposition 3.8 is exactly `(PNS2)`.  Since `B` is infinite, the
canonical conditional expectation shows that the crossed-product Fourier
summands give infinitely many orthogonal right `M^B` modules, so
`[Q:M^B]=infinity`.  The already established CDI index calculation handles
the smaller input coordinate `M^e`.  Proposition 3.8 explicitly places
`w_(b,c)` in `U(M^B)`, rather than in a finite scalar group.  These facts
exclude every projective core actually named by the construction.  Remark
1.1 confirms that no alternative group-factor envelope theorem is claimed.

The displayed conclusions exhaust the structural objects supplied in the
four cited constructions.  They do not rule out an unnamed subfactor, which
is why the claim is stated as a source audit rather than an abstract
nonexistence theorem.
