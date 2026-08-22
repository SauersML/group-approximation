---
rg: 2
id: toeplitz-range-commutator-has-a-balanced-mirror-exit
kind: claim
title: The Toeplitz range commutator preserves the Hilbert hotel but admits a balanced finite mirror exit
artifacts:
  - research/artifacts/toeplitz-compressed-covariance-mirror-exit-2026-08-21.md
distinct_from:
  full-label-chord-normalization-kills-the-hilbert-hotel: that forces the chord into a fixed label normalizer and thereby destroys both the spectator and infinite completeness; this keeps the exact unilateral-shift model but proves that the natural compressed word has no finite soundness.
  fanizza-reflection-recurrence-has-s4-stationary-overlap: that exhibits a stationary overlap hidden by a symmetric-difference word; this exhibits the equal-rank mirror exit forced by trace cyclicity for a conjugate range projection.
  central-corner-block-is-not-a-group-word: that proves an abstract controlled additive block is not a word; this identifies the precise one-sided support block forgotten by the Toeplitz reflection commutator.
---

Let `H<=E` be projections, put `F=E-H`, and let `T` be an ambient unitary.
Write

```text
R_E=1-2E,       Q=TET^*,       R_Q=T R_E T^*.           (TRC1)
```

The natural ordinary-word shadow of a unilateral range inclusion is

```text
[R_E,R_Q]=[R_F,R_Q]=1,          R_F=1-2F.               (TRC2)
```

It is exact in the properly infinite model where `TET^*=F<E`.  It does not
control the missing projection in finite matrices.

Indeed, in any finite amplification choose a projection `C<=1-E` with
`rank(C)=rank(H)`, put

```text
Q=F+C,                                                   (TRC3)
```

and choose a symmetry `T` which fixes `F`, swaps `H` with `C`, and is the
identity on the remaining complement.  Then `TET^*=Q`, all of `E,F,Q`
commute, and `(TRC2)` has zero defect.  Nevertheless, for

```text
X=FTE                                                     (TRC4)
```

one has

```text
X^*X=F,             E-X^*X=H.                            (TRC5)
```

Thus the compressed Gram saturates the guarded rank floor while the mirror
exit `C=(1-E)Q` absorbs exactly the missing finite rank.  Its density can be
any prescribed positive rational density allowed by the fixed C18 carrier;
there is no boundary dilution in this countermodel.

Trace cyclicity gives exactly the wrong conclusion for the proposed
payment.  Whenever `E,Q` commute and `Q=TET^*` in a finite tracial algebra,

```text
tau(E(1-Q))=tau((1-E)Q).                                (TRC6)
```

It balances the desired missing cell `H=E(1-Q)` against the mirror cell
`C=(1-E)Q`; it does not make either cell small.

This blindness holds for every ordinary word using only the two range
reflections.  In the proper nested model the three nonzero joint spectral
cells have reflection characters

```text
F:       (-1,-1),
H:       (-1,+1),
1-E:     (+1,+1).                                      (TRC7)
```

These three characters separate `C_2 times C_2`.  Hence any word
`w(R_E,R_Q)` which is the identity in that model is already the trivial word
in `C_2 times C_2`, and therefore remains the identity after adjoining the
fourth mirror character `(+1,-1)`.  No collection of such words can express
the oriented inclusion `Q<=E`.

The translation reset and coordinate-Pauli localization leave this model
unchanged: place `E,H,F,C,T` in the reset/residual factor and all old-spin
Paulis in an independent factor.  The reset fixes the label type vector,
while `C` occupies its scalar multiplicity reservoir.  Therefore a
compressed-covariance proof still needs to force the one-sided block

```text
(1-F)TE=0                                                (TRC8)
```

or an equivalent mirror-exit payment.  Equation `(TRC8)` is an additive
corner relation, not an ordinary word in `R_E,R_F,T`; replacing it by
`(TRC2)` loses precisely the orientation needed for the one-sided rank
argument.  The stronger word `R_F=T R_E T^*` does remove the mirror, but it
is literal full projection conjugacy.  The canonical tracial firewall then
forces `tau(E)=tau(F)` and kills `H`; it does not preserve the marked cell.
