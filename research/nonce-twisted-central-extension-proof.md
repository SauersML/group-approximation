---
rg: 2
id: nonce-twisted-central-extension-proof
kind: route
title: Apply Thom's all-central-character criterion to the phase-range extension
target: nonce-twisted-factor-gives-nonhyperlinear-group
requires:
  - thom-central-corner-criterion
---

The set of cocycle values is countable because `Gamma x Gamma` is countable,
so the subgroup `C` that it generates is countable.  The displayed
multiplication therefore defines a countable group `Gamma_tilde`, with
central subgroup `C x {e}`, quotient `Gamma`, and classifying cocycle
`omega`.

Let `iota:C -> T` be the inclusion character.  The twisted sector belonging
to `iota` is exactly

```text
L_(iota o omega)(Gamma) = L_omega(Gamma),
```

which is non-Connes-embeddable by hypothesis.  Thom's Lemma 3.3, recorded in
`thom-central-corner-criterion`, says that a group with central subgroup `C`
is hyperlinear if and only if *every* character sector of its quotient is
Connes embeddable.  The `iota` sector fails that test, hence `Gamma_tilde` is
not hyperlinear.

This argument does not realize the bad sector as a positive-trace corner of
`L(Gamma_tilde)`: when `C` is infinite its central-character fiber can have
zero Plancherel measure.  Thom's criterion is precisely the stronger theorem
that makes such a corner unnecessary.

