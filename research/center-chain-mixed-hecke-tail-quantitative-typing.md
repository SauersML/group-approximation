---
rg: 2
id: center-chain-mixed-hecke-tail-quantitative-typing
kind: claim
title: Quantitatively type the mixed center-chain Hecke polars as the two native occurrences
distinct_from:
  center-chain-hecke-flags-authenticate-native-occurrences: that invalidated claim asks for one fixed exact group-algebra carrier and row; this asks only for representation-dependent finite-matrix spectral cuts, with every discarded direction charged to approximate relation defects.
  center-chain-mixed-hecke-polars-share-a1-tail: that proves the exact polar words and identifies their selector-root squares, but also exposes why the common A1 suffix is not already a common gauge.
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that regular-trace firewall is a required boundary condition here; the cuts in this claim may depend on the matrix model and are not asserted to survive in the canonical regular representation.
  center-chain-mixed-hecke-overlap-is-common-pauli-source: that now gives an exact common source and range, maximal polar overlap there, and a relative gauge whose sole Pauli action is the first selector root; this claim retains only the missing identification with the prescribed native selector covariances.
---

**OPEN REPRESENTATION-DEPENDENT NATIVE-COVARIANCE SEAM.**  For every sufficiently good
finite-dimensional normalized-Hilbert--Schmidt model of the fixed chained
packet, take the four approximate Hecke compressions and the two mixed
cross-Grams of `center-chain-mixed-hecke-polars-share-a1-tail`.  Construct
representation-dependent spectral support cuts `q_1,q_2` and polar maps
`V_1,V_2` such that, after discarding total normalized trace
`O(delta^alpha)` for some fixed `alpha>0`, all of the following hold:

1. `V_i^2` is close on `q_i` to the prescribed literal coefficient root
   `x_87(s_(00)t_0)` or `x_98(s_(000)t_(00))`, respectively;
2. the source and target cuts retain the native relative ranks
   `(1/2,1/4)` and `(1/4,1/8)` up to `O(delta^alpha)`;
3. the common right `A_1` tail in the polar normal forms can be removed or
   synchronized on a positive common source cut, with its first-row
   commutator charged to the first selector relation rather than silently
   treated as a commuting reservoir gauge; and
4. the resulting two transports have a positive cross-Gram support and the
   mixed source-Pauli estimates required by
   `binary-leavitt-native-two-scale-cross-gram-positive`.

Here `delta` is the maximum normalized Hilbert--Schmidt defect of the finite
set of packet and native-row relations used in the construction.  The cuts
must be functorial only at the level of each matrix model; no fixed nonzero
projection in the group algebra is allowed.  This finite-only formulation is
exactly what avoids the regular-trace contradiction.

## Attempts

- **Exact common source and tail factorization.**
  `center-chain-mixed-hecke-overlap-is-common-pauli-source` now proves that
  the range-overlap product is a projection, that both pullbacks are one
  source Pauli corner of relative trace `1/128`, and that the relative polar
  factors as `B_2R`, where `R` lies exactly in the source-Pauli commutant and
  the Pauli action of `B_2` is exactly the first selector root.  Thus scalar
  overlap, spectral support, common-tail separation, and both mixed-Pauli
  tests are no longer open inside the Hecke packet.  What remains is the
  actual native-row covariance: correct Hecke ranks and literal selector
  roots still do not identify the four Hecke flags with the prescribed
  source and controlled-target projections of the two unequal selector
  occurrences.

- **Fixed exact flags.**  The four exact supports have precisely the desired
  ranks, but `fixed-center-chain-hecke-occurrence-is-regularly-impossible`
  proves that attaching both native rows to a fixed positive carrier forces
  the incompatible affine values `theta=1/2` and `theta=5/6`.
- **Literal Whitehead restriction.**  On the largest corner reducing both
  native Whiteheads, `A_2=+1`; the two A-side polars collapse while the
  Whiteheads remain distinct.  This is the exact countermodel in
  `native-whitehead-corner-collapses-hecke-flags`.
- **Mixed polar squares.**  The new exact calculation gives
  `(B_2A_1)^2=x_87(s_(00)t_0)` and
  `(B_3A_2A_1)^2=x_98(s_(000)t_(00))`, so the correct coefficient roots are
  finally present.  The unresolved coupling is asymmetric: `A_1` commutes
  with `B_3A_2` but not with `B_2`.  A viable proof must turn this exact
  commutator into a quantitative defect payment or a model-dependent
  spectral split; declaring `A_1` a common tensor gauge repeats the refuted
  fixed-row argument.
