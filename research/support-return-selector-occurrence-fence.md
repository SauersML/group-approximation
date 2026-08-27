---
rg: 2
id: support-return-selector-occurrence-fence
kind: claim
title: The authenticated support-return odd loops do not supply the unequal selector rows
artifacts:
  - experiments/support_partial_whitehead_native_return_audit.py
distinct_from:
  support-return-gives-gauged-native-loop: that proves the two exact odd factorizations of the native Whiteheads; this classifies the label actions of every occurrence in those factorizations and fences their use as the missing unequal selector rows.
  support-return-charts-meet-in-two-pauli-pairs: that computes the exact intersection of the transported charts; this combines that intersection with the native and Hecke source-row audits to state the occurrence-typing consequence.
  quarter-whiteheads-lack-unequal-source-conjugacy: that audits the two literal native Whiteheads on the fixed chart; this also audits the inner support-return words on their transported charts and the relative chart word on the common subpacket.
---

**ESTABLISHED FINITE-MENU OCCURRENCE FENCE.**  Use the notation of the
support-return identities

```text
J_i=W_i Khat_i W_i,       Khat_1=Z_1H_1Z_1,
                          Khat_2=Z_2H_2Z_2.             (SRO1)
```

Let `E` be the fixed three-pair same-center Pauli group and
`E_i=W_iEW_i`.  Among the literal group-word occurrences in `(SRO1)`, none
authenticates target label fractions `1/4,1/8` on one common three-pair
carrier:

1. `J_1,J_2` normalize `E`, but both act there as adjacent transpositions.
   Their negative label fractions are therefore `1/4,1/4`, not
   `1/4,1/8`.
2. `W_1,W_2` do not normalize `E`, so they have no label fractions on the
   fixed three-pair packet.
3. `Khat_i` normalizes only `E_i`.  Conjugating `(SRO1)` by `W_i` shows that
   its action on `E_i` is conjugate to the adjacent-transposition action of
   `J_i`, hence again has negative label fraction `1/4`.
4. The exact intersection `E_1 intersect E_2` is only a two-pair Pauli
   group.  On it the relative word `S=W_1W_2` is label-trivial.  Thus this
   common reduction discards the third bit needed for a rank-one
   `C_(1/8)` label and leaves the relative reservoir gauge arbitrary.

The source side is absent as well.  The named center-chain Hecke supports
have the scalar ranks `1/2,1/4,1/8`, but their reflections are analytic
group-algebra elements, not the source reflections of an ordinary
group-word conjugacy.  On the largest corner reducing both native
Whiteheads, the two relevant Hecke target maps become equal while the two
Whiteheads remain distinct quarter swaps.  Consequently no row in the
authenticated support-return menu has the form

```text
U_1 R_(1/2) U_1^*=C_(1/4) tensor V_1,
U_2 R_(1/4) U_2^*=C_(1/8) tensor V_2                 (SRO2)
```

with ordinary word occurrences on one common positive three-pair carrier.
This is a scope statement about the displayed support-return, native
Whitehead, and named Hecke menu; it does not rule out a new mixed
occurrence outside that menu.

There is an exact finite gauge witness to the missing identification.
Tensor the two chart transporters independently by central signs
`epsilon_1,epsilon_2 in C_2`.  Each odd identity `(SRO1)` contains its
transporter sign twice, so both `J_i` and their Coxeter braid are unchanged.
The relative word acquires the arbitrary sign `epsilon_1epsilon_2`, which
is invisible on the label-trivial two-pair intersection.  Hence the
authenticated equations do not identify the two transported-chart gauges
and cannot imply `(SRO2)`.

The remaining occurrence seam is therefore exact: a new word relation
must retain all three Pauli pairs and either provide a literal odd
one-eighth controlled reflection or identify one transported chart with a
typed unequal-scale selector chart.  The support-return factorizations
alone do neither.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
support-return-selector-occurrence-fence-proof
