---
rg: 2
id: marked-star-asymmetric-heads-have-half-quarter-sources
kind: claim
title: Asymmetric Hecke returns cut the marked star by one half and one quarter but compose their gauges
artifacts:
  - research/marked-star-asymmetric-head-support-proof.md
distinct_from:
  marked-star-outer-corrected-whiteheads-are-quarter-swaps: that supplies conjugate quarter-label gauges on the full positive star carrier; this computes the source flags produced by the first uncancelled native b2 and b3 returns.
  center-chain-four-hecke-flags-have-native-ranks: that obtains the four desired fractions from fixed Hecke compressions on a nonabelian signed character atom; this obtains the half/quarter source pair representation-universally on the positive commuting marked-star carrier, but no quarter/eighth target pair.
  b2-b3-pair-full-hecke-four-native-sectors: that quarters the full signed Hecke source with two commuting native signs and then equalizes the two source marginals; this quarters the star source by composing two asymmetric return heads and changes the second reservoir gauge to their product.
  native-whitehead-hecke-head-has-order-seven-anchor: that gives one odd order-seven anchor for each individual Whitehead/head pair; this proves why the quarter source requires a cumulative head not covered by either individual anchor.
  projective-row-data-do-not-authenticate-hecke-polars: that leaves independent involutory spectator gauges on two separately projective rows; this gives an exact common S3 reservoir where the two individual gauges are conjugate but their cumulative gauge is a three-cycle.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs the half/quarter sources together with quarter/eighth outputs carrying conjugate involutory gauges; this establishes the sources but shows the naturally attached second gauge is a product rather than the second involution.
---

Retain the marked-star carrier `E`, anchored Pauli pairs, and
outer-corrected transports `U_1,U_2` from
`marked-star-outer-corrected-whiteheads-are-quarter-swaps`.  Distinguish the
anchored Pauli `Z` arms

```text
Z_2=x_82(b_2),                  Z_3=x_92(b_3)          (ASH1)
```

from the asymmetric center-chain heads

```text
H_1=x_84(b_2)x_47(a_1),
H_2=x_95(b_3)x_58(a_2).                               (ASH2)
```

Then the single-head compression has exact common source and range support

```text
supp|(E H_1 E)|=R_1=E(1+Z_2)/2,
tau(R_1)=tau(E)/2.                                    (ASH3)
```

The second individual head similarly has support `E(1+Z_3)/2`, again of
relative rank one half.  The native quarter source appears only after
composing the two asymmetric returns.  Put

```text
T_21=E H_2H_1 E.
```

Its source and range supports are

```text
T_21^*T_21=R_++=E(1+Z_2)(1+Z_3)/4,
T_21T_21^*=R_-+=E(1-Z_2)(1+Z_3)/4,                    (ASH4)
```

so both have relative rank `1/4`.  Thus `(R_1,R_++)` is a literal nested
half/quarter source flag on the positive marked-star carrier, valid for
every finite-dimensional trace profile.  No canonical character moments
are used.

This does not finish the selector typing.  The conjugate reservoir
involutions `V_1,V_2` belong to the outer-corrected words
`U_i=L_iJ_i`, not to the asymmetric heads.  The order-seven relation instead
contains the uncorrected word `J_iH_i`.  Although `J_i` preserves `E`, it
does not normalize the marked-star Pauli packet: it sends an anchored
`A` arm to the forked arm with the old outer index.  Moreover `H_i` does
not preserve `E`; only its compression is a partial isometry.  Consequently
the exact seventh-power word cannot be restricted to the star carrier to
identify the polar gauge of `EH_iE` with `V_i`.  This is the same leakage
boundary recorded in `native-whitehead-hecke-head-has-order-seven-anchor`,
now at a positive carrier with explicitly computed support.

Even under the strongest favorable extra identification, namely that the
two individual compressed heads carry the braided gauges `V_1,V_2`, the
cumulative quarter map in `(ASH4)` carries reservoir factor

```text
V_2V_1,                                                (ASH5)
```

not `V_2`.

Take `V_1,V_2` to be the two adjacent transpositions in the standard `S_3`
representation.  They are conjugate involutions and satisfy the braid,
while `V_2V_1` is a three-cycle.  Thus braid/conjugacy alone cannot turn the
composite head holonomy into the second involutive gauge.  Separately, the
order-seven relation cannot repair this mismatch on `E`: attaching the same
commuting involution to both factors of the uncompressed row cancels it in
`J_iH_i`, whereas the compressed star row is not a reducing occurrence of
that product.  All support formulas `(ASH3)--(ASH4)` are spectator-invariant.

Consequently one asymmetric return supplies only a half source.  Two
returns supply the desired quarter source, but their polar holonomies
compose rather than automatically reusing the second native gauge.  The
smallest remaining occurrence must compare `H_2H_1` with one individual
second-scale transport by an odd identity-outer row, or otherwise remove
the first head holonomy while preserving the quarter source.  Neither the
outer-corrected braid nor the two separate, nonreducing order-seven anchors
performs that comparison.

The half/quarter support statement is an exact consequence of the literal
binary-Leavitt group words.  The `S_3` argument is a sharp fence on what the
available braid data can imply; it is not asserted to extend to a
representation of the full binary-Leavitt Steinberg group.  No Property
`(T)`, Kazhdan input, literature theorem, local heavy computation, or Lean
compilation is used.

DERIVATION
marked-star-asymmetric-head-support-proof
