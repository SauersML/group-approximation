---
rg: 2
id: same-center-whitehead-native-selector-subcorner-attachment
kind: claim
title: Attach the two native selector occurrences to the conjugate Whitehead gauges on a positive model-dependent subcorner
distinct_from:
  same-center-whitehead-gram-extracts-transport-gauges: that constructs the two analytic candidates after removing adjacent swaps; this asks that the actual native selector outputs agree with those candidates on one positive reducing subcorner.
  same-center-whitehead-gram-is-not-native-selector-gram: that proves the full Gram of the two reducing Whitehead unitaries does not supply this attachment; this is the precisely fenced additional matrix-only statement.
  exact-whitehead-selector-gauge-attachment-collapses-packet: that rules out imposing both unequal rows exactly on the whole fixed packet isotypic carrier; this permits a representation-dependent finite-matrix subcorner and charges all discarded mass by ordinary word defects.
  binary-leavitt-native-two-scale-cross-gram-positive: that permits any authenticated positive polar overlap of the two native rectangular transports; this asks specifically that the same-center Whitehead gauges are the external gauges of the two selector outputs.
---

**OPEN OCCURRENCE-TYPING SEAM.**  In every positive-density active-core
operator-norm microstate of

```text
Delta=St_20(L_(F_2)(1,2)),       z=x_13(s_1t_1),
```

let `F`, `V_1,V_2`, and `T_i^cand` be the common carrier, conjugate
Whitehead reservoir gauges, and analytic candidates of
`same-center-whitehead-analytic-candidate-package`.  Extract a reducing
subprojection `P<=F`, depending on the matrix coordinate, such that

```text
tau(P) >= gamma tau(F)-o(1)                            (SNA1)
```

for one fixed `gamma>0`, and authenticate the two **actual** native selector
occurrences on `P` as

```text
T_1^native|_P = (C_(1/4) tensor V_1)|_P + o_2(1),
T_2^native|_P = (C_(1/8) tensor V_2)|_P + o_2(1).      (SNA2)
```

The source support rows must retain negative fractions `1/2` and `1/4` on
the corresponding normalized carriers.  The errors and the mass loss must
be controlled by a fixed finite list of ordinary Steinberg word defects,
independently of ambient matrix dimension.

Neither analytic multiplication by the label reflections, equality of the
prefix coefficient names, nor the tautological full Gram of two unitaries
counts as `(SNA2)`.  The subcorner must be genuinely model-dependent: exact
fixed-word attachment of both unequal rows on the whole packet carrier is
excluded by the regular-trace firewall.

## Attempts

- **Wordize the one-eighth label as a commutator of two controlled Pauli or
  adjacent-Whitehead occurrences.**  This is impossible already on the
  recovered `M_8(C)` label by
  `same-center-m8-commutators-cannot-wordize-one-eighth-reflection`.
  The desired rank-one reflection has determinant `-1`, whereas every
  ordinary label commutator has determinant `+1`.  Two independent Pauli
  half-controls produce a rank-two, one-quarter reflection because the
  payload qubit remains free.  Cutting that last qubit would assume the
  missing joint-control occurrence.  The adjacent braid does not remove the
  other obstruction: it makes `V_1,V_2` conjugate but need not make them
  commute, as the two standard `S_3` transpositions show.  Hence `(SNA2)`
  needs a direct odd-determinant mixed occurrence, or a same-gauge
  identity-outer anchor, rather than a two-word commutator repair.

- **Identify the same-center Whiteheads with the native Whiteheads.**  This
  identification is literal, not a root-position conjugacy:

  ```text
  W_1=J_1=x_87(x_1)x_78(y_1)x_87(x_1),
  W_2=J_2=x_98(x_2)x_89(y_2)x_98(x_2).
  ```

  Hence the factors `V_i` are already the reservoir gauges of the two
  native partial Whitehead words on `F`; there is no additional transporter
  `R_i` and no two-sided chart-gauge freedom at this step.  This still does
  not prove `(SNA2)`: both literal words act by adjacent swaps with negative
  label fraction `1/4`, whereas the controlled selector rows required in
  `(SNA2)` have fixed label factors `C_(1/4)` and `C_(1/8)` and retain
  distinct source fractions.  On the natural common reducing Hecke corner,
  `native-whitehead-corner-collapses-hecke-flags` proves that the two Hecke
  polars become equal while `J_1,J_2` remain the two adjacent swaps.  Thus
  word equality authenticates the native Whitehead occurrences but does
  not attach them to the unequal controlled selector outputs.

- **Keep both literal quarter-label Whiteheads and import only the unequal
  source ranks.**  This conditional affine endpoint is valid and stronger
  than `(SNA2)`: if actual source reflections of negative fractions
  `1/2,1/4` were conjugated to `W_1,W_2` themselves, the two common
  `q=1/4` rows would force the conjugate gauge parameter to equal both
  `1/2` and `1`.  But
  `quarter-whiteheads-lack-unequal-source-conjugacy` audits the named
  native and Hecke rows and finds no such conjugacy.  The Hecke source flags
  have the correct ranks only as occurrence-untyped compressed supports and
  do not even begin on the same literal carrier as the same-center packet.
  Replacing those supports by `1-2r_i` would introduce analytic
  group-algebra reflections rather than actual existing word occurrences.
  On the largest corner reducing both Whiteheads, `(CNW9)` collapses the two
  Hecke target maps while the Whiteheads remain distinct quarter swaps.
  Imposing the missing conjugacies on the whole fixed carrier merely invokes
  the exact affine firewall.  Thus this shortcut removes `C_(1/8)` only
  conditionally and does not remove occurrence typing.

- **Find an odd relation using only the common Pauli carrier.**  This is
  impossible at the group level:
  `same-center-pauli-actors-have-whitehead-sign-quotient` maps every Pauli
  actor to `+1` and both native adjacent Whiteheads to `-1`.  The exact
  three-qubit sign twist preserves all internal packet rows while changing
  each `J_i` by operator norm `2`.  The known odd order-seven heads evade
  the quotient only by using center-chain actors which eject the packet;
  compressing those actors back to this carrier is the unresolved moving
  return/leakage problem.

- **Use the authenticated support-return odd loops as the two selector
  rows.**  The identities

  ```text
  J_i=W_i(Z_iH_iZ_i)W_i
  ```

  are literal group-word identities on the recentered carrier and are the
  first successful odd returns of both native coefficients.  However,
  `support-return-selector-occurrence-fence`
  classifies every occurrence in this finite menu.  The `J_i` are both
  quarter-label adjacent swaps; each inner word is another quarter-label
  swap on a different transported chart; and the two transported charts
  meet in only two Pauli pairs, where their relative transporter is
  label-trivial.  The named Hecke source ranks remain analytic and
  occurrence-untyped.  Thus the odd loops authenticate native Whitehead
  occurrences but still do not furnish the `1/4,1/8` target-label pair or
  the two ordinary source conjugacies required by `(SNA2)`.

- **Dress one Whitehead transport by an ordinary root mover and cut the
  resulting positive cross Gram.**  The root-valued overlap theorem proves
  the scalar Gram only after the dressed full-word occurrences have been
  named.  It does not remove the dressing.  The exact finite packet
  `root-valued-overlap-does-not-undress-external-selector` makes the root
  overlap and Gram maximal while the mover is the scalar `-1` on the entire
  marked carrier.  Every positive subcorner then pays squared comparison
  error `4tau(P)`.  Hence a root-valued relative word can close the scalar
  leaf of `binary-leavitt-arbitrary-profile-native-cross-gram`, but cannot by
  polar calculus alone prove `(SNA2)`.  A positive proof still needs an
  ordinary native relation which fixes the parity of the individual dressed
  occurrence.

- **Use the row-two quarter source on an irreducible actor constituent.**
  This fails with the sharpest possible operator-norm gap.
  `row2-quarter-source-opnorm-two-fence` chooses a nontrivial irreducible
  reservoir constituent for the recentered five-pair actor packet.  The only
  packet-reducing projections are zero and the whole carrier, and the actual
  `J_2` has strictly larger negative rank than every quarter-source
  reflection.  Their conjugacy defect is exactly two.  Hence no positive
  model-dependent subcorner recovers row two from the current
  braid/order-seven/recentered packet; a new mixed occurrence must remove
  the actor holonomy.

- **Make the marked coefficient act on the actual row-two arm and return it
  through a constant Whitehead.**  This is now literal.  With
  `C_3=[A_3,B_3]=x_65(q)` one has

  ```text
  [C_3,A_2]=x_68(qa_2)=x_68(a_2)=w_65(1)A_2w_65(1)^(-1).
  ```

  `row2-marked-center-action-return-has-gl8-model` nevertheless realizes
  this mixed occurrence together with both prefix actors and both
  order-seven heads in a marked `GL_8(F_2)` chart.  Even independently
  factoring both returned paths does not help:
  `row2-parallel-a2-return-diamond-has-gl8-model` includes the two literal
  `s_1,t_00` commutator paths and a factor-by-factor Weyl comparison, yet the
  same model survives by identifying separately named coefficients in the
  same root subgroup.  A continuation must attach that returned arm to the
  unequal Hecke source projection or add a coefficient row which forbids
  those same-root identifications; another root-position diamond is below
  the occurrence seam.

  The full presentation does forbid the particular equality used by that
  `GL_8` model.  `native-t00-y1-collision-pays-marked-opnorm` proves that
  `D=x_78(t_00+s_0t_00)` has a fixed normal return to `z`, so it has positive
  overlap with the marked carrier and forces maximal separation of the two
  arms there.  This is not yet `(SNA2)`: the `GL_10` model of
  `marked-t00-separation-has-gl10-model` retains the paid distinction and
  stores it outside every named signed-Hecke source.  The next occurrence
  must localize `P_zP_D` to the row-two source or make source escape pay.
  The literal attachment `[D,B_2]` has also been tested:
  `native-t00-collision-first-hecke-attachment-has-gl10-model` ejects the
  full-rank-scale `t_1` direction while preserving the same exact marked
  chart and order-seven head.  This proves that Hecke-arm contact without a
  named source compression still does not establish `(SNA2)`.

- **Move the marked root by an external Weyl and retain both Pauli charts.**
  The root-valued relative word is exact, but the chart mover is not erased.
  `six-pair-chart-swap-retains-external-gauge` gives a full `M_64(C)` label
  model in which all six Pauli pairs and every mixed commutator are exact,
  while the external chart swap contributes a scalar `-1` only to the
  dressed second occurrence.  Hence no positive subcorner makes its gauge
  conjugate to the undressed first gauge.  An ordinary odd word must type
  the chart swap as part of the actual `1/8` row; analytic chart enlargement
  is insufficient.

- **Use a dual-Heisenberg spectator to make the dressed outputs share a
  gauge.**  This changes the operators whose Gram is being measured, not the
  raw affine targets.  The exact model in
  `spectator-dressed-gram-does-not-share-selector-gauges` realizes both raw
  affine rows with the incompatible gauge fractions `1/2,5/6` and gives the
  dressed outputs maximal Gram with a trivial common spectator gauge.
  Therefore the dressed overlap does not imply `(SNA2)` without an ordinary
  word relation comparing the raw outputs or removing the spectators.
