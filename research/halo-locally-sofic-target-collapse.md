---
rg: 2
id: halo-locally-sofic-target-collapse
kind: claim
title: Halo witnesses with locally sofic targets collapse to sofic-class witnesses
distinct_from:
  single-lamps-recover-set-action: That is class-agnostic and argues through the lamp coordinates; this argues through the finite generation of a single witness and applies to an arbitrary automorphism action, but only when the targets happen to be locally sofic.
  coordinate-action-not-sofic: That refutes the sofic-action hypothesis for one action; this says that for a large family of target classes the hypothesis is not even a weaker condition than the sofic one.
artifacts:
  - notes/FALSE_HALO_ACTION_AUDIT.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

If an automorphism action has Alekseev--Bradford witnesses whose target groups
are **locally sofic**, then it is already a sofic sofic-action in their sense.

Consequently, for the Kun--Thom coset action, no witness with locally sofic
targets exists at all:

```text
the Kun--Thom action has no locally-sofic target witnesses.      (HAA5)
```

## Which targets this covers

Every alphabet one would naturally reach for when trying to enrich a halo
witness:

- **finite-dimensional unitary labels.** Every finitely generated subgroup of
  `U(n)` is a finitely generated linear group, hence residually finite by
  Malcev, hence sofic. So `U(n)` is locally sofic.
- **Pauli and Clifford labels.** Finite Clifford groups are finite.
- **direct products and matrix amplifications** of the above, which do not
  change the conclusion at any fixed finite action test.

So the "richer labels" idea is not merely blocked; the labels are not richer.

## Consequence

Both factors of `W = (directSum_(G/Gamma) C_2) semidirect G` are sofic — the
lamp group is locally finite and `G` is residually finite. If the Kun--Thom
action admitted witnesses of this kind, Alekseev--Bradford's semidirect-product
theorem for the sofic class would make `W` sofic, contradicting
`wreath-not-sofic`. Hence `(HAA5)`.

The audit draws the sharp conclusion: any genuine hyperlinear-action proof must
have, at some finite test, a target `Lambda_0` that is itself a finitely
generated hyperlinear nonsofic group — which is the main problem again. The
halo framework is a good permanence result *after* a seed exists and cannot
manufacture the first one.
