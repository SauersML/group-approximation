---
rg: 2
id: binary-leavitt-el20-arbitrary-profile-native-cross-gram
kind: claim
title: The two native binary transports overlap on every surviving EL20 operator-norm profile
distinct_from:
  binary-leavitt-arbitrary-profile-native-cross-gram: that states the corresponding theorem for St20 and therefore retains a possible central Steinberg-lift phase; this works directly in the manuscript's elementary-group lane, where the order-seven anchors are literal matrix identities.
  binary-leavitt-native-two-scale-cross-gram-positive: that is a canonical-trace normalized-HS claim; this is quantified over every arbitrary normalized trace profile arising from a norm-corona representation.
---

**OPEN DIRECT-ELEMENTARY MF CROSS-GRAM CLAIM.**  Every norm-matrix-corona
homomorphism from

```text
G=EL_20(L_(F_2)(1,2))
```

which retains `z=e_13(s_1t_1)` has, after positive-density active
reblocking, two actual native unequal-scale transports

```text
S_1,S_2:P_source H_n -> P_target H_n
```

and constants `gamma,c>0` satisfying

```text
tr_n(S_1^*S_2S_2^*S_1)>=gamma tr_n(P_source)-o(1),
tr_n(P_source)>=c,                                      (EAP1)
```

with the two mixed source-Pauli commutators of the relative polar gauge
tending to zero.  The transports must be the prescribed rows with ratios
`1/2 -> 1/4` and `1/4 -> 1/8`, not unrelated rectangular completions.

The quantifier is over arbitrary operator-norm profiles.  Canonical group
trace moments, Property `(T)`, Kazhdan correction, and literature inputs are
not available.

## Attempts

The original order-seven route through one common reducing cut is refuted:
`el20-order-seven-heads-force-zero-common-hecke-reducing-cut` forces that cut
to vanish, and `order-seven-first-exit-is-not-seven-step-leakage` shows that
the proposed one-exit estimate did not control a seventh-power telescope.

The surviving route is
`order-seven-growing-multicut-gives-el20-native-cross-gram`.  Its only open
input is `growing-multicut-el20-order-seven-inheritance`, but moving cuts do
not by themselves finish the argument.  The exact fence
`moving-order-seven-stage-gauges-have-coboundary-drift` shows that seven
transported conjugates of one nontrivial gauge may have trivial cyclic
product.  The live requirement is therefore an EL20 coefficient-sensitive
fixed-Hecke-frame lock (equivalently, asymptotic commutation with the
reservoir holonomy), in addition to the moving boundary control.

**Quantifier shift (swarm-0917).**  The arbitrary-profile quantifier is not
needed for the EL20 MF endpoint.
`surviving-mf-mark-diracizes-to-canonical-opnorm-profile` takes any surviving
model and forms conjugate tensor powers.  Because `EL_20(R)` is simple and
perfect, the scalar kernel of a nontrivial MF character is trivial.  The
result is a DIFFERENT surviving operator-norm model with `tr -> delta_e`,
Plancherel multiplicities on every finite packet, and negative carrier of `z`
of trace `1/2+o(1)`.  Hence the specialization
`binary-leavitt-el20-canonical-opnorm-native-cross-gram` `(CAP1)` suffices,
via the new route `el20-canonical-opnorm-cross-gram-gives-full-mf-radical`.

This repairs, for EL20, the missing premise found by
`canonical-cross-gram-does-not-close-arbitrary-mf-active-profile`.  That node
asked for an intrinsic argument forcing the finite-packet profile, and this is
one.

- **What it removes.** Fences whose countermodels use non-Plancherel packet
  profiles are irrelevant to the endpoint.
- **What it leaves.** The occurrence-typing and coboundary-gauge obstructions
  remain, because regular packet models already realize them.

`(EAP1)` itself is not proved, and this node stays OPEN.

**Entropy-measure transplant and the order-seven gauge kill
(swarm-0917-w15-w15-ptm-pull, transplanter, 2026-09-19).**

- **The entropy transplant dies a priori.**  The plan was to replace the
  cross-Gram overlap by an entropy or Haar-measure count on the canonical
  profile.  After the Dirac reduction above, the Haar-averaged packet
  measure is the regular character: trace `delta_e`, Plancherel
  multiplicities, and carrier of `z` of trace `1/2`.  So every
  measure-theoretic estimate it produces is also satisfied by `lambda`.  By
  `native-cross-gram-conclusions-fail-in-every-tracial-model`, `lambda`
  fails the gauge-lock clause.  The transplant therefore cannot supply
  `(EAP1)` and is dead at the gauge-lock clause.
- **The surviving route is also dead as a decomposition.**
  `order-seven-gauge-trivialization-contradicts-selector-rank` proves the
  row-wise floors `delta_1+||1-D_1||_2^2/4>=1/2` and
  `delta_2+(3/8)||1-D_2||_2^2>=1/4` in every finite von Neumann algebra.
  Both are tight on the OAP gauges.  The conclusion `D_i=1+o_2(1)` of
  `(GMC3)` contradicts the selector row that `E_0` must retain, separately
  for each row.  The same holds for the outputs of
  `el20-six-moving-coefficient-square-bridges`, through the six-square lock.
  So GMI and ESB are equivalent to the endpoint.  No relator-charged EL20
  word can satisfy `(ESB2)` in any exact tracial model; the canonical
  profile has exactly such a limit.  The recorded "bridge retains a gauge"
  failures are all forced.
- **What remains.**  A non-tracial input, such as operator-norm
  integrality, must enter before `(ESB2)`.  This node stays OPEN only in
  that vacuous sense.
