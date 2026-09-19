---
rg: 2
id: endpoint-odd-actor-retains-native-factor-gauge
kind: claim
title: The endpoint odd actor retains a paired native-factor gauge
artifacts:
  - research/endpoint-odd-actor-factor-gauge-proof.md
distinct_from:
  endpoint-order-five-actor-has-half-gram: that proves a representation-universal positive Gram for the literal endpoint Whitehead; this proves that its order-five factorization does not identify the individual native Hecke factor.
  full-packet-cyclic-aggregates-retain-positive-endpoint-gram: that retains positive Gram after making the order-five or order-seven carrier invariant; this shows that invariant aggregation still depends only on the product word and cannot recover its two factors.
  native-whitehead-hecke-head-has-order-seven-anchor: that kills a reservoir involution attached to either the Whitehead or the Hecke head separately; this records the simultaneous paired gauge which cancels before that seventh-power test.
---

**ESTABLISHED FACTORIZATION-GAUGE FENCE.**  Retain the literal second
native head and endpoint actor

```text
v_2=B_3A_2,             M=J_2v_2,             C=WM,
M^7=C^5=W^2=1.                                      (EOG1)
```

Let `D` be a central multiplicity involution for this finite occurrence
interface.  The simultaneous replacement

```text
J_2 -> J_2D,                 v_2 -> v_2D             (EOG2)
```

preserves the individual involutive/conjugation data seen by the interface
and, crucially,

```text
(J_2D)(v_2D)=J_2v_2=M.                                (EOG3)
```

It therefore fixes `W,M,C`, all their relators, their action on the
four-root group `V`, and every spectral projection or orbit join constructed
only from that action.  In particular it fixes the signed endpoint cuts
`p_2,p_*`, both cyclic aggregates `E_C,E_M`, and the endpoint compression
and polar supplied by the established positive-Gram theorems.

The mixed Hecke word has the literal factorization

```text
u_2=v_2A_1.
```

Keeping `A_1` fixed in `(EOG2)` changes its exposed factor by

```text
u_2 -> u_2D.                                           (EOG4)
```

Thus the data in `(EOG1)`, even together with the full `GL_4(F_2)`/
returning-`GL_3(F_2)` endpoint action and either positive cyclic aggregate,
does not algebraically type the endpoint polar as the `J_2`, `v_2`, or
`u_2` occurrence.  On a nonzero `D=-1` multiplicity block the two possible
values in `(EOG4)` are operator-norm distance `2`, so passing to a positive
subcorner cannot make the ambiguity vanish.

This does not contradict the order-seven coercivity formula.  That formula
detects `D` when it is attached to only one of `J_2,v_2`; the paired change
in `(EOG2)` cancels before the order-seven word is evaluated.  It also does
not refute the full arbitrary-profile native cross-Gram claim: additional
ordinary Steinberg relations may couple one factor oddly to a typed source
or target.  It proves that the new endpoint order-five relation and cyclic
aggregates alone are not that missing coupling.

Any continuation using this actor must therefore supply an ordinary
occurrence with odd incidence in exactly one of the two factors in `(EOG2)`,
or directly authenticate the source and target Grams of `u_2`.  Reusing
`C=WM`, taking a polar, or making its carrier cyclically invariant cannot
remove the paired gauge.

No Property `(T)`, canonical trace, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
endpoint-odd-actor-factor-gauge-proof
