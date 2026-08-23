---
rg: 2
id: involutory-opposite-root-face-obeys-projective-transfer
kind: claim
title: The involutory opposite-root face obeys a dimension-free denominator transfer inequality
distinct_from:
  root-additivity-eliminates-the-s3-rank-one-leak: that is an exact case analysis inside one finite group; this gives a robust normalized-Hilbert--Schmidt inequality in arbitrary matrix dimension on the order-two root face.
  sl3-rank-one-denominator-self-commutator-removes-target-phase: that starts from small target projective energy and removes its scalar phase; this bounds the target commutator directly from root torsion, denominator-relation defect, and root centrality.
  fixed-projective-gap-forces-primary-congruence-mass: that places an enemy in positive p-primary mass after an exact congruence correction; this directly excludes the bottom exponent-two root face without assuming an exact correction.
---

Let `U,H,a,b` be unitaries in a finite matrix algebra and put

```text
R=a^2 (H b^(-2) H^*) a b a^*.
```

With normalized Hilbert--Schmidt norm define

```text
eta=||H-R||_2,
alpha=||a^2-I||_2,       beta=||b^2-I||_2,
epsilon_a=||Ua-aU||_2,   epsilon_b=||Ub-bU||_2.          (IOR1)
```

Then

```text
||UHU^*H^*-I||_2
 <=2(eta+alpha+beta)+2 epsilon_a+epsilon_b.              (IOR2)
```

In particular, if the literal opposite-root variables are involutions,
`U` centralizes them, and the rank-one denominator identity is exact, then
`[U,H]=1`. The estimate is dimension independent.

For the dyadic arithmetic lane this closes the conductor-one/root-exponent-
two face of the raw rank-one packet. Any surviving finite counterpacket must
retain positive mass where at least one of the two opposite-root variables
has genuinely deeper two-power order (or pay one of the explicit terms in
`(IOR2)`). Rank-two Steinberg gluing is therefore needed to synchronize
those deeper strata, not to handle the bottom involutory stratum.

