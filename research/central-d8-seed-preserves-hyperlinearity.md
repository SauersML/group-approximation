---
rg: 2
id: central-d8-seed-preserves-hyperlinearity
kind: claim
title: A central D8 seed preserves and reflects hyperlinearity
distinct_from:
  infinite-character-actor-kills-fd-mark: that proves the seed is invisible in every finite-dimensional representation under an aperiodicity hypothesis; this proves that adjoining the seed cannot be the first source of nonhyperlinearity.
  pauli-lamplighter-over-stable-codense-kazhdan-pair: that uses two Pauli generators centralized by a stabilizer and one transported commutator; this treats the single central D8 seed attached to one involution.
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that is the general finite graph-of-groups permanence theorem; this identifies the exact graph-of-groups normal form of the marked seed used by the infinite-character route.
  whitehead-clifford-graft-hyperlinear-iff-base: that computes the same permanence principle for one large controlled-Clifford/affine-Leavitt graft and adds a regular-model support firewall; this gives the universal two-generator D8-seed normal form for an arbitrary group and involution.
---

**ESTABLISHED.**  Let `G` be a countable group and let `1!=b in G` be an
involution.  Form

```text
P(G,b)=<G,z,J | z^2=J^2=1, J central, [b,z]=J>.          (CDS1)
```

Then

```text
P(G,b) ~= (G x <J>) *_(<b,J>) D_8,                      (CDS2)
```

where `D_8=<b,z,J | b^2=z^2=J^2=1, J central,
[b,z]=J>` has order eight and the common edge group
`<b,J> ~= C_2 x C_2` is finite.  In particular the two vertex groups embed,
`J!=1`, and

```text
P(G,b) is hyperlinear  <==>  G is hyperlinear.           (CDS3)
```

Thus the central Pauli seed used in the infinite-character construction is
an exact **detector**, not a source, of nonhyperlinearity.  If a
word-energy argument proves the marked group `P(M rtimes A,m_0)`
nonhyperlinear, it has simultaneously proved that the unmarked
actor--module group `M rtimes A` is already nonhyperlinear.  Conversely, no
hyperlinear actor--module base can be made nonhyperlinear merely by this D8
attachment, even when the seed is killed by every exact finite-dimensional
representation of the marked group.

The last clause separates finite-dimensional invisibility from the desired
matrix-microstate obstruction.  The former is supplied by an aperiodic
character action; the latter must occur in the base's diffuse/approximate
module sector, because finite-edge amalgamation preserves Connes
embeddability.
