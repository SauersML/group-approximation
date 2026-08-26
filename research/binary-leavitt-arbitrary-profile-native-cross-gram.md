---
rg: 2
id: binary-leavitt-arbitrary-profile-native-cross-gram
kind: claim
title: The native binary transports overlap on every surviving operator-norm active profile
distinct_from:
  binary-leavitt-native-two-scale-cross-gram-positive: that is restricted to canonical-trace normalized-HS microstates; this is quantified over every positive-density active core obtained from an arbitrary norm-corona representation and may use operator-norm exactification.
  opnorm-leavitt-coarse-fine-return-row: that asks for one operator-norm support row on a nonzero possibly sparse carrier; this asks only for positive normalized-HS cross-Gram mass on the positive-density reblocked active core.
  coherent-heisenberg-multiplicity-decoder: that reconstructs a complete approximate binary Leavitt module; this asks only for the two native selector transports and their relative Pauli gauge.
---

**OPEN MF-NATIVE SCALAR HOLONOMY CLAIM.**  Let an arbitrary homomorphism
from

```text
Delta=St_20(L_(F_2)(1,2))
```

to a norm matrix corona retain `z=x_13(s_1t_1)`.  Apply
`torsion-normal-generator-has-full-support-corona-core` and choose
operator-norm asymptotic matrix lifts on the resulting active core.  Without
assuming canonical trace moments for any nonidentity word, exactify the fixed
depth-one and next-refinement Pauli packets and obtain the two **actual**
native scale transports

```text
S_1,S_2:P_source H_n -> P_target H_n.
```

Prove constants `gamma,c>0`, depending only on the fixed presentation packet,
such that

```text
tr_n(S_1^*S_2S_2^*S_1) >= gamma tr_n(P_source)-o(1),  (APG1)
tr_n(P_source) >= c,                                  (APG2)
```

and the two mixed source-Pauli commutators of the relative polar gauge are
`o(1)` in normalized Hilbert--Schmidt norm.  The estimates must hold for the
arbitrary normalized characters carried by the reblocked norm-corona model;
regular/canonical finite-packet multiplicities may not be inserted.

This is the cross-Gram statement sufficient for the Property-`(T)`-free MF
radical route.  Operator-norm relator defect may be used to exactify each
fixed packet, and then normalized-HS spectral cuts may be used on its
positive-density carrier.  What is forbidden is replacing the model's trace
profile by the canonical group trace.

The existing direct root-overlap theorem remains available uniformly over
these profiles: every fixed nonzero disjoint root has a positive overlap with
the marked carrier after active reblocking.  The unresolved content is to
authenticate the two unequal-scale selector occurrences on that overlap, or
to derive an equivalent strict-capacity collision for their own source and
target projections.  Fixed center-chain Hecke fractions computed from
`tau(e_chi)=1/64` do not meet this quantifier.

No Property `(T)`, Kazhdan projection, canonical-trace hypothesis, or
literature theorem is permitted in this claim.

## Attempts

- **Import the center-chain Hecke fractions.**  This fails at the quantifier:
  their values use the regular character atom `tau(e_chi)=1/64`, whereas an
  arbitrary active norm-corona profile may concentrate on different finite
  packet types.  Operator-norm exactification preserves that multiplicity
  vector rather than regularizing it.
- **Use only the uniform direct root-overlap floor.**  This gives a fixed
  positive slice of each named nonzero root inside the marked carrier, but
  two such slices can remain disjoint and are not yet the source/target Grams
  of the native selector occurrences.  The typed rectangular packet realizes
  this escape.
- The live attack is therefore an arbitrary-profile occurrence compiler:
  couple the literal unequal-scale coefficient roots to the fixed marked-root
  overlaps by a mixed/opposite-root row, or prove a strict capacity deficit
  for their own exactified source and target projections.  This is deferred
  while the operator-norm atomic three-row route is tested in parallel.
- **Use a root mover to dress one same-center Whitehead candidate and then
  polar-cut its cross Gram.**  This does give the scalar overlap for the
  dressed word, but does not authenticate it as the undressed native
  occurrence.  `root-valued-overlap-does-not-undress-external-selector`
  gives an exact marked transporter packet with maximal root overlap and
  maximal cross Gram in which the dressing is `-1` on every positive
  subcorner.  Thus the root-valued alternative remains sufficient only once
  the actual full-word occurrence typing is supplied independently.
- **Cut a nonidentity prefix-normalizer orbit after active reblocking.**
  `free-s3-atom-has-unit-opnorm-leakage` gives a marked arbitrary-profile
  type on which the active projection is the whole carrier but every
  nonidentity `S_3` normalizer moves a character atom orthogonally.  Every
  nonzero subcut has operator-norm return leakage exactly one, even after
  amplification.  Thus density and coordinate dependence do not turn the
  authenticated adjacent-swap menu into `(APG1)`; a new identity-action or
  root-valued relative occurrence must exclude or pay this free orbit.
- **Search the authenticated native occurrence closure for the root-valued
  relative word.**  `native-local-occurrence-closure-fixes-mark` makes this
  search exact: every named prefix factor, return diamond, support loop,
  Hecke head, and same-center Pauli arm has root indices disjoint from
  `{1,3}`.  Their whole subgroup centralizes `z`, so no pair already in that
  closure can meet the disjoint-root alternative.
- **Adjoin the smallest external Weyl root mover.**  The literal word
  `h=w_14(1)w_23(1)` exchanges `z=x_13(q)` with `x_42(q)`, and
  `external-weyl-dressed-native-pair-is-root-valued` therefore makes
  `(W_1,hW_2)` a genuine root-valued pair with full Gram on `P_zP_C`.
  It also moves every endpoint of the second Pauli chart.  Enlarging to both
  charts does not repair this typing: the exact six-qubit model of
  `six-pair-chart-swap-retains-external-gauge` satisfies both chart
  covariances, the braid, root exchange, full Gram, and all mixed commutator
  tests while the exposed gauges remain the scalars `+1` and `-1`.
  Thus the external mover must be tied to the actual unequal selector by an
  additional odd occurrence; combined-chart factoriality alone does not
  prove `(APG1)` for the native transports.
- **Dress the two affine rows by a dual-Heisenberg spectator and compare the
  dressed Grams.**  `spectator-dressed-gram-does-not-share-selector-gauges`
  separates the two operations which this shortcut conflates.  Right
  dressing a conjugator by a source-central spectator preserves its row but
  leaves the target affine gauge unchanged; multiplying the target changes
  the gauge but defines a different row.  A `96`-dimensional exact model has
  maximal dressed Gram and a shared trivial dressed gauge while its raw
  selector gauges have positive fractions `1/2` and `5/6`.  Hence a
  same-packet dual frame does not close the scalar holonomy claim without an
  ordinary undressing/raw-output comparison occurrence.
