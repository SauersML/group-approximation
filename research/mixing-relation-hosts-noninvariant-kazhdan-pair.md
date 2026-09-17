---
rg: 2
id: mixing-relation-hosts-noninvariant-kazhdan-pair
kind: claim
title: Some free mixing action of a sofic group has a Kazhdan infranormal pair in its full group with a non-invariant fixed algebra
distinct_from:
  f2xf2-admits-mixing-nonsofic-action: that asks for a nonsofic mixing action of one fixed group by any mechanism; this asks for one specific certificate, a full-group Kazhdan pair, in the relation of any sofic group
  simple-group-lattice-admits-nonsofic-action: that asks for a nonsofic seed for a Howe--Moore lattice; this needs no seed action of the acting group
---

**OPEN.** There are a countable sofic group `G`, an essentially free mixing p.m.p. action `G ↷ (X,μ)`, and
countable sofic groups `Γ <= L`, both Kazhdan with `Γ` infranormal in `L`, together with a homomorphism
`ρ : L → [R_G]` such that `L^∞(X)^(ρ(Γ))` is not `ρ(L)`-invariant.

By `full-group-kazhdan-pair-noninvariant-fixed-algebra-is-nonsofic`, this settles
`mixing-free-nonsofic-action-of-sofic-group`.

**Constraints already known.**

* `ρ(Γ)` cannot be (a restriction of) a subgroup of `G`, because mixing makes it ergodic.
* If `ρ(L)` acts on a positive set as the free Kun--Thom action of a Theorem E pair and trivially elsewhere,
  `G` needs infinite elementary abelian `p`-subgroups (`kun-thom-actions-have-no-host-without-p-torsion`). The
  host relation must also carry a `ρ(L)`-invariant finite subrelation outside the copy
  (`kun-thom-action-soe-class-is-rigid`, clause 3).
* No Bernoulli shift of a sofic group hosts such a pair. Its relation is sofic, so the certificate cannot
  fire.

**Open design space.** Non-free `ρ`: for example `ρ(L)` acting on `A` through a factor of a generalized
Bernoulli action over `L/Γ`, with nontrivial stabilizers, so that the copy is not a free Kun--Thom
relation. The host `G` is unconstrained apart from soficity and mixing, and it may contain `L` as a
subgroup acting mixingly, in addition to the non-subgroup copy `ρ`.
