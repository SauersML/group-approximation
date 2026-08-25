---
rg: 2
id: center-chain-hecke-flags-authenticate-native-occurrences
kind: claim
title: Identify the nested center-chain Hecke flags with the two native selector occurrences
distinct_from:
  center-chain-hecke-polar-supports-are-nested-pauli-flags: that completely computes the two Hecke operators, their common polar corner, and their Pauli gauge; this asks for the remaining typed identification with the prescribed unequal-scale selector rows.
  same-center-whitehead-gram-is-not-native-selector-gram: that refutes typing two equal quarter-label Whitehead swaps as the quarter/eighth pair; this asks whether the genuinely unequal quarter/eighth Hecke flags can be inserted into the actual native occurrences.
---

**OPEN OCCURRENCE-TYPING SEAM.**  In the fixed chained-root packet of
`center-chain-hecke-polar-supports-are-nested-pauli-flags`, prove that the
two stabilized native selector-row transports for

```text
s_(00)t_0,                    s_(000)t_(00)             (CHF1)
```

restrict on one fixed positive carrier to the polar maps of

```text
eA_1e,                       eA_2A_1e,                  (CHF2)
```

with label support projections `p_1,p_2` and with only the allowed fixed
Pauli source/target relabelings.  Equivalently, construct the finite
ordinary-word row which identifies the coefficient occurrences in `(CHF1)`
with the nested Hecke flags in `(CHF2)` without replacing either prescribed
selector by an unrelated rectangular completion.

The entire analytic part is already exact: the two support fractions are
`1/4,1/8`, their cross-Gram has relative mass `1/8`, the smaller support
reduces the source Pauli pair, and the relative polar gauge lies exactly in
its commutant.  What remains is solely the Leavitt/Steinberg occurrence
identification required by the native-row definition.

## Attempts

- **Substitute the literal selector roots.**  The actual chained-root words
  carrying `(CHF1)` are the cross-commutator roots
  `x_87(s_(00)t_0)` and `x_98(s_(000)t_(00))`.  They centralize `H`, so their
  compression to `e` has full support `e`, not the nested supports
  `p_1,p_2`; `center-chain-scalar-gram-polar-cut-returns-moving-atom` shows
  that their polar cut returns exactly the nonreducing atom.  Thus they do
  not identify `(CHF2)`.
- **Declare the two Hecke supports to be the label projections.**  The
  fractions and Pauli covariance are correct, but this supplies no ordinary
  selector-row word conjugating the prescribed source reflections to the
  two controlled targets.  The affine rank obstruction starts only after
  those two row relations have been authenticated.  Treating equal traces
  as that conjugacy would repeat the typing error fenced by
  `hecke-quarter-selector-is-untyped-or-rank-preserving`.
- The next viable attack must therefore build a fixed Whitehead/Steinberg
  occurrence row linking each literal coefficient root to the corresponding
  Hecke polar map, while preserving the smaller `p_2` corner.  That finite
  word construction is deferred; it is now the only missing part of this
  route.
