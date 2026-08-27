---
rg: 2
id: fanizza-verifier-d16-charger-globalizes-ground-support
kind: claim
title: The D16 charger reads the Fanizza Hamiltonian only by globalizing its ground sector
distinct_from:
  uniform-clock-reflection-block-encodes-game-hamiltonian: that constructs the coherent verifier reflection and computes its uniform-zero-flag compression; this diagonalizes the same reflection in the transverse flag basis and tests the D16 commutator on it.
  hadamard-selector-commutator-charges-two-path-leakage: that gives the exact charger for an already wordized selector-central return; this identifies the Fanizza blocks and proves that the available HALT support and the native doubling paths do not provide that input.
  fanizza-reflection-recurrence-has-s4-stationary-overlap: that gives an exact finite stationary model for the multiplicative recurrence shadow; this locates the missing Boolean-AND reflection which the verifier charger would have to wordize.
---

# The D16 charger reads the Fanizza Hamiltonian only by globalizing its ground sector

ESTABLISHED.  Write the coherent verifier reflection as

```text
C=sum_j e_(jj) tensor ((1-L_j) tensor 1+L_j tensor X).  (FDC1)
```

Use the `X`-eigenbasis on the flag and let `z=X`.  Then `C` commutes with
`z` and has the exact selector blocks

```text
C=diag(I,R),
R=sum_j e_(jj) tensor (1-2L_j).                         (FDC2)
```

Thus the D16/Hadamard calculation does apply formally.  Its transverse
commutator has squared normalized Hilbert--Schmidt defect

```text
||[h C h,z]-1||_2^2
 =||I-R||_2^2
 =4 (1/M) sum_j tau(L_j).                              (FDC3)
```

So the cell reads the full game Hamiltonian with a dimension-independent
constant.  This is not yet the required group cell for two exact reasons.

First, the native signal carrier of the verifier is

```text
Q=q_s tensor (1+Z)/2,                                  (FDC4)
```

which is transverse to the `X` selector and is not invariant under `C`
unless all the losing projections vanish on the relevant space.  The
recorded HALT witness supplies only a ground vector

```text
H_m xi=0,                    <xi,D_R xi>>0,             (FDC5)
```

not a packet or group-algebra projection of positive canonical mass on
which every `L_j` vanishes.  Imposing the D16 commutator as a global group
relator makes `(FDC3)` zero in every exact representation and therefore
forces

```text
L_j=0                         for every j,              (FDC6)
```

as operators.  This globalizes the ground-sector condition beyond the
available HALT completeness theorem.  Localizing the relator to the support
of `(FDC5)` would require exactly the missing word-visible common
ground/source projection.

Second, `(FDC2)` does not contain the two successive Fanizza doubling paths.
For one recurrence cell put

```text
P=P_n,             S=X_n P_n X_n^*,
Z=1-2P,            Y=1-2S.                             (FDC7)
```

The desired payment is the overlap projection `PS`.  Since the ordinary
word shadow only forces `[Z,Y]=1`, the reflection which would let `(FDC3)`
charge that overlap is

```text
1-2PS.                                                   (FDC8)
```

It is not a word in `Z,Y`: on the four joint characters its values are
`(+1,+1,+1,-1)`, whereas every word in the Klein four group is a character
and has a multiplicative parity truth table.  The exact stationary `S4`
model realizes all four joint characters with positive mass, so this is not
remedied by the multiplicative recurrence relations.  It is precisely a
controlled Boolean-AND group-algebra element.

Consequently the coherent verifier offers a useful analytic identity but
does not itself supply the selector-central ordinary return required by the
D16 charger.  The minimal positive interface is a matrix-decoded,
word-visible projection `E` of positive controlled mass such that
`E L_j=0` on the exact HALT model and the commutator can be charged only on
`E`.  This is the common-source/Gram localization sought by
`capacity-gated-common-source-gram-word-cell`; for the native triangle its
proper-return analogue is `single-triangle-trace-cyclic-return-cell`.

