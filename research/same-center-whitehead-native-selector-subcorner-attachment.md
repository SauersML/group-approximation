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
  moving-signed-source-does-not-localize-paid-sheet-detector: that proves the paid moving source, both literal sheet detectors, and the forced order-seven exit still do not name an unequal target Gram; this asks for exactly the mixed full-Gram attachment left open by that fence.
  endpoint-detector-cell-retains-coboundary-gauge: that transports a complete endpoint detector/probe mark-return occurrence through a fresh same-center braid but leaves full overlapping ranges and a coboundary reservoir frame; this asks for the proper fixed-frame unequal attachment excluded there.
  two-endpoint-source-intersections-retain-character-square: that intersects both endpoint source types and retains an exact orthogonal four-character square even after all endpoint detector classes are imposed; this asks for the native attachment which must break that twist.
  endpoint-whiteheads-are-center-chain-hecke-spectators: that places the endpoint braid on the literal quarter/eighth Hecke supports and gets the correct one-eighth cross-Gram, but only because the braid centralizes those supports; this asks for the noncentral raw-row attachment absent there.
  endpoint-whitehead-hecke-flag-trichotomy: that enumerates all coordinate collisions with the two Hecke flags; the unique fine-only collision has flexible, possibly zero overlap and leaves its polar gauge entirely in the reservoir.
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
  Signed Reynolds averaging sharpens this to the exact alternative in
  `paid-t00-carrier-has-signed-hecke-reynolds-dichotomy`: source compression
  keeps norm greater than one, or an explicit detector word pays at least
  one half.  The detector is not a relator, and
  `paid-t00-carrier-can-miss-row2-source` realizes the segregated branch.
  Hence `(SNA2)` still needs an ordinary occurrence identifying that branch
  with a native row defect.

  Exhausting the eight constant-atom conjugates does not add such an
  occurrence.  `paid-pauli-menu-has-two-row2-indistinguishable-sheets`
  collects them to the two values `D,DH`, with
  `H=x_73(t_1+s_0t_1)`.  This `H` commutes with the actual
  `T,A_2,B_2,B_3,J_2` packet and its order-seven head, so the entire named
  row transports the two choices in parallel and gives the same first
  Hecke commutator on both.  The minimal marked three-qubit fence separates
  the paid equal-scale atom from a noncollapsed row-two summand.  Therefore
  a continuation must genuinely detect this sheet root or impose source
  incidence; freezing one of the eight words along a subsequence is not
  occurrence typing.

  The factor-level detection half is now established.
  `row2-source-factor-detects-paid-pauli-sheet` descends through the literal
  row relation `[S_57,T]=A_2` and obtains the nonzero cube face

  ```text
  [S_57,H]=[[S_57,D],Y_2]
          =x_53(s_1t_1+s_1s_0t_1).
  ```

  Hence the authenticated factor closure distinguishes `D` from `DH` even
  though every composite named above is blind.  This still does not prove
  `(SNA2)`: the paid atom is not known to reduce `S_57`, and the new `x_53`
  carrier has not been placed on the actual signed quarter/eighth source.
  The remaining seam is precisely that source incidence or a quantitative
  charge for the `S_57` leakage.

  There is now a valid moving-source incidence statement, but it stops one
  typing later than `(SNA2)` requires.
  `paid-cut-has-moving-hecke-source-or-detector` conjugates the full signed
  source by the frozen paid Whitehead word.  Unless one conjugated detector
  pays at least one half, the paid overlap produces a positive
  approximation-dependent `R_0<=Q`, and either literal Hecke word `u_i`
  carries `R_0` into the common range `P` with zero boundary.  The exact
  EL20 commutator forces

  ```text
  10||(1-R_0)t_1R_0||_2+4||(1-R_0)t_2R_0||_2
    >=sqrt(tau(R_0)),
  ```

  so this is genuinely a moving cut, not the forbidden common reducing
  corner.  It still does not establish `(SNA2)`: after refinement to `Q`,
  both Hecke maps have the same range `P`, and the native quarter/eighth
  target Grams are absent.  In the detector-free branch the exact next seam
  is to control the `S_57` boundary while carrying `R_i` to the actual
  row-two source/target flag; in the detector branch it is a
  relation-controlled upper bound on that paying word.  A tautological
  conjugate cut leaves the reservoir coboundary free and cannot substitute
  for either transition.

  Taking the polar part of the positive source incidence does not move this
  seam.  `paid-polar-bridge-does-not-type-moving-hecke-target` shows that
  the polar range can lie in the Whitehead-reducing cut with full positive
  support while having zero Gram with both literal Hecke targets.  The raw
  ordinary-word-authenticated moment remains `Q_sC_sEaEC_sQ_s`; the polar
  normalization itself is analytic and cannot be declared a typed row.

  The detector-side root search is now finite and complete, but the same
  typing seam remains.  `five-return-legs-cover-hecke-detectors-not-source-gauge`
  exhausts the `31` root-free positive classes: the three middle returns
  cover `28`, and `x_12(s_1),x_14(s_1)` cover the other three.  None of the
  useful first probes preserves `Q`; it only names one of `24` conjugate
  source types.  On the three endpoint classes the exact mark scale profile
  for every same-`g` occurrence is `{3}`, with no adjacent pair, because
  `J_m` fixes `x_1r(a_m)` rather than carrying it to `x_1r(a_(m+1))`.
  Therefore neither the complete root menu nor the existing braid controls
  the reservoir coboundary in `(SNA2)`.  A continuation must add a fresh
  endpoint-Whitehead `Jhat_(r,m)` carrying `x_1r(a_m)` to
  `x_1r(a_(m+1))` and type its multiplicity action on the moving source/range
  occurrence.

  The fresh endpoint words themselves are no longer open.
  `endpoint-whitehead-profile-has-maximal-gram-overlap` proves their exact
  coefficient transport and full source/range Grams.  Iterating them gives
  the six-state `S_3` profile, not an expanding selector compiler: both
  incoming transports onto any profile type have the identical whole range,
  so their cross-Gram has squared mass `tau(Q_k)`.  Thus formal branching
  degree `2` is exactly cancelled by the Gram leakage, while selecting one
  edge gives only a permutation cycle.  A regular `S_3` reservoir makes all
  edge gauges nontrivial coboundaries satisfying every braid relation.  The
  remaining requirement in `(SNA2)` is therefore a proper-subrange or
  fixed-frame occurrence typing, not endpoint transport by itself.

  This remains true after inserting the detector/probe cube itself.
  `endpoint-detector-cell-retains-coboundary-gauge` starts with the exact
  ordinary identity

  ```text
  [x_12(a_3),[g_3,Y_3]]=z
  ```

  and conjugates the detector, probe, source and both endpoint arms through
  the fresh braid.  Thus endpoint coefficient transport and complete
  occurrence typing are both available.  What is absent is precisely the
  conclusion of `(SNA2)`: all edges still have the whole moved source and
  target as their Grams, and a regular `S_3` multiplicity model keeps the
  reservoir factors as nontrivial coboundaries.  No restriction of this
  transported cube names the native quarter/eighth outputs.

  Nor can `(SNA2)` be obtained by intersecting the `r=2` and `r=4`
  endpoint sources.  `two-endpoint-source-intersections-retain-character-square`
  computes a common nontrivial character annihilating both intersection
  subgroups and realizes four orthogonal source charts.  The two moved
  endpoint sources have zero meet with the fixed signed source, while all
  three exceptional detector commutator cells persist exactly.  Hence even
  the simultaneous two-endpoint packet leaves the reservoir frame
  undetermined; a successful attachment must break this character twist by
  an ordinary fixed-frame mixed Gram.

  Even the literal nested Hecke supports do not make this cube noncentral.
  `endpoint-whiteheads-are-center-chain-hecke-spectators` uses the endpoint
  chain `(10,11,2)` and proves exact commutation of both fresh Whiteheads
  with the center-chain atom, both flag groups, and both Hecke arms.  The
  compressed words on the quarter/eighth supports consequently have
  cross-Gram support exactly `p_2`, of relative trace `1/8`.  This is the
  correct scalar number but the wrong occurrence type: it is a commuting
  spectator dressing, so its regular `S_3` reservoir gauge remains free and
  the fixed regular-trace model satisfies every displayed equation.  A
  solution of `(SNA2)` must therefore couple one endpoint/native word oddly
  to an individual Hecke polar; scalar compression by the fixed flags is
  not enough.

  No alternative endpoint placement repairs this.
  `endpoint-whitehead-hecke-flag-trichotomy`
  proves the complete incidence classification.  Touching coordinate `7`
  ejects the quarter support; avoiding `7,8` is the spectator case; touching
  `8` alone preserves `p_1` but sends the extra fine root
  `x_68(a_2)` to a new root.  The resulting fine compression has exact polar
  `What p_*`, but `p_*` has no positive arbitrary-profile lower bound: an
  exact swapped-character block has nonzero `p_2` and zero `p_*`.  Whenever
  it survives, both fine label involutions are scalar `+1`, so the complete
  Whitehead factor is again an uncontrolled reservoir gauge.  This is an
  equal-rank fine-to-fine covariance, not either unequal row in `(SNA2)`.

  Nor does intersecting one moved source with the original signed source
  create a fixed-frame subcorner.
  `endpoint-whitehead-signed-source-has-only-relative-hecke-overlap` proves
  that the pair intersection is exactly the endpoint-isolating subgroup,
  of order `256` for endpoint `2` and `512` for endpoint `4`.  The associated
  canonical Hecke coefficients are positive, but a two-character exact
  profile has zero meet between the two source projections.  Every constant
  signed normalizer dressing still gives a full, maximally overlapping edge,
  while the inverse Whitehead only cancels its own gauge.  Thus this relative
  Hecke overlap is not the positive fixed subcorner required by `(SNA2)`.

  There is also no hidden fixed-source adjacent pair obtained by multiplying
  the exceptional actors.  The full finite closure in
  `exceptional-endpoint-detector-products-stay-at-depth-three` is a positive
  order-eight subgroup generated by `x_26(1)`, `x_29(1)`, and
  `x_46(1)x_49(1)`.  Its endpoint columns meet the native depth list
  `(7,8,9)` only at `9`.  Hence all of its mark-return cells have depth
  `3`, so multiplication and `L_0` conjugacy cannot supply the two fixed-`Q`
  rows required by `(SNA2)`.

  Exhausting all positive actors reveals exactly how far this fixed-source
  idea goes.  By
  `positive-signed-actor-two-scale-profile-is-partial-and-gauged`, `184` of
  the `511` positive classes have a depth-two/depth-three endpoint incidence,
  and `x_28(1)x_49(1)` gives an explicit pair of nested mark-return cells on
  `Q`.  The remaining `327` classes include all `31` root-free detector
  classes.  Moreover the explicit pair uses two independent commuting
  factors and its two edge gauges admit independent spectator dressings.
  It therefore supplies neither the uniform paying-detector alternative nor
  the common target Gram required by `(SNA2)`.

  The simultaneous endpoint/prefix swap provides the expected global
  conjugacy but not the missing subcorner.
  `simultaneous-endpoint-prefix-whitehead-moves-source-before-locking-gauge`
  constructs an involution fixing `g_*` and transporting both arms of its
  depth-two cell to depth three.  This involution moves `Q`; the two signed
  groups meet in order `16`, and their regular Hecke overlap
  `tau(Q)/512` can have zero meet in an arbitrary exact character profile.
  Hence its conjugacy relates the cell over `Q` to the next cell over the
  moved source.  No cross commutator returns that chart to the fixed source,
  so `(SNA2)` remains open.

  The post-moving-source boundary is now exact in
  `moving-signed-source-does-not-localize-paid-sheet-detector`.  The
  common-tail detector `K_Q=[A_1,H]` has a signed-character model in which
  it is globally nontrivial, mark-conjugate, and equal-rank, yet acts as the
  identity on all of `Q`; consequently it acts trivially on every extracted
  `R_0<=Q` and its Hecke conjugate acts trivially on `R_i`.  The shorter
  `S_57` cube has only global rank control and introduces the uncontrolled
  boundary `||(1-R_0)S_57R_0||_2`.  Thus neither sheet detector turns the
  forced order-seven exit into the missing unequal target Gram.  The next
  input must be the ordinary mixed full-Gram row stated in `(MSD7)`, not a
  further global root-saturation argument.

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

- **Make every signed-Reynolds detector small by relator telescoping.**
  `signed-reynolds-detectors-form-the-marked-complement-subgroup` proves
  that the `8192` detector words are the graph of `lambda_0` inside the
  genuine direct product `<z> directProduct L_0`.  They form a faithful
  subgroup isomorphic to `L_0`; only the identity detector is a relator.
  In the regular representation all defining relators vanish while every
  nonidentity detector has operator-norm distance two from the identity,
  also on the negative marked sector.  Thus the detector branch of the
  Reynolds dichotomy cannot be removed by bounded-area presentation
  telescoping.  The remaining positive use of that dichotomy must exploit
  its source-compressed discrepancy or a new paid-subcorner incidence.
