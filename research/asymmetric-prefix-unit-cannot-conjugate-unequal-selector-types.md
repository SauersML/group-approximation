---
rg: 2
id: asymmetric-prefix-unit-cannot-conjugate-unequal-selector-types
kind: claim
title: The asymmetric prefix unit cannot conjugate the unequal selector label types
artifacts:
  - research/asymmetric-prefix-unit-selector-type-fence-proof.md
distinct_from:
  asymmetric-prefix-unit-conjugates-native-whiteheads: that proves the exact raw occurrence identity GJ_1G^(-1)=J_2 and types its moved source and target Grams; this audits whether the same conjugator can carry the complete Pauli/controlled-selector typing from the first native row to the second.
  asymmetric-prefix-unit-misses-fixed-hecke-frame: that detects movement of the fixed signed Hecke source by root-position incidence; this gives an independent representation-theoretic obstruction even after allowing a moved carrier and an arbitrary reservoir gauge.
  quarter-whiteheads-lack-unequal-source-conjugacy: that audits whether other named covariance rows attach unequal source ranks to the two equal-quarter Whiteheads; this rules out obtaining the unequal quarter/eighth target labels by extending the asymmetric conjugacy itself.
  center-chain-four-hecke-flags-have-native-ranks: that computes the four numerical ranks without occurrence typing; this proves why conjugacy of the raw Whiteheads cannot supply that missing typing.
---

**ESTABLISHED ASYMMETRIC-CONJUGACY FENCE.**  Retain the exact ordinary
EL20 identity

```text
GJ_1G^(-1)=J_2                                      (ASC1)
```

from `asymmetric-prefix-unit-conjugates-native-whiteheads`.  On the
three-qubit Pauli label factor, both raw native Whiteheads are adjacent
swaps.  Each therefore has label negative fraction `1/4`.  Equation
`(ASC1)` is an exact quarter-to-quarter occurrence conjugacy, even though
its coefficients come from unequal prefix depths.

The two controlled selector rows require different typed label data:

```text
row 1: source 1/2, target 1/4,
row 2: source 1/4, target 1/8.                         (ASC2)
```

The same `G` cannot extend `(ASC1)` to a conjugacy of the complete typed
rows.  Indeed, let the recovered Pauli label algebra on a nonzero carrier
be

```text
P=M_8(C) tensor 1_M.
```

If `G` does not carry the first complete Pauli packet to the second, then it
already fails to be a packet occurrence transport.  If it does, its
restriction is a unital star-isomorphism of `M_8(C)`, hence preserves the
normalized label trace and the rank of every label spectral projection.
It can therefore carry a label reflection only to another reflection with
the same negative fraction.  In particular it cannot carry

```text
C_(1/4) to C_(1/8),        or        R_(1/2) to R_(1/4).  (ASC3)
```

Allowing an arbitrary multiplicity gauge does not change this conclusion.
After identifying the two irreducible Pauli packets, every packet
normalizer has the form

```text
W_label tensor V_res.
```

Thus it conjugates the label reflection by `W_label` and the reservoir
factor by `V_res` separately.  Moving the Hecke carrier from `F` to
`F'=GFG^(-1)` also preserves the relative label rank.  A reservoir sign can
at most replace a label reflection by its negative, changing a fraction
`q` to `1-q`; neither `1/4` nor its complement `3/4` is `1/8`.

Equivalently, for label reflections `C_q=1-2P_q`, the elementary projection
rank bound gives

```text
inf_U ||U C_(1/4) U^* - C_(1/8)||_2^2 >= 1/2,
inf_U ||U R_(1/2) U^* - R_(1/4)||_2^2 >= 1,           (ASC4)
```

where the norm and trace are normalized on the eight-dimensional label
factor.  Hence there is a fixed exact type gap, not a missing perturbative
estimate.

Consequently the asymmetric prefix unit supplies the raw identity
`J_1 -> J_2` and its moved-source Gram square, but it does not authenticate
the prescribed `1/4` versus `1/8` controlled-selector outputs, nor the
`1/2` versus `1/4` sources.  Those reflections remain analytic support
projections from the center-chain Hecke calculation, not literal outputs of
`(ASC1)`.  A valid continuation must add a separately typed native
occurrence on a model-dependent positive subcorner; it cannot obtain the
second row by conjugating the complete first row with `G`.

This fence does not rule out such a lossy subcorner construction.  It rules
out only the proposed exact extension of the asymmetric prefix conjugacy to
the full controlled-selector/Pauli packet.  No Property `(T)`, canonical
trace substitution, local computation, or literature theorem is used.

DERIVATION
asymmetric-prefix-unit-selector-type-fence-proof
