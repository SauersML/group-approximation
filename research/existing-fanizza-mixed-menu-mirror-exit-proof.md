---
rg: 2
id: existing-fanizza-mixed-menu-mirror-exit-proof
kind: route
title: Put the scalar reset spectator in the conjugate complement and evaluate every existing row
target: existing-fanizza-mixed-menu-leaves-balanced-mirror-exit
requires:
  - translation-reset-leaves-a-compressed-gram-spectator
  - inside-corner-hecke-tests-miss-the-asynchronous-mirror-exit
  - toeplitz-range-commutator-has-a-balanced-mirror-exit
  - fanizza-full-reflection-row-has-sharp-mirror-floor
  - full-label-chord-normalization-kills-the-hilbert-hotel
---

Fix one negative-central-character reset label representation on `V`, with
packet cuts

```text
H_0<=E_0,       F_0=E_0-H_0,
h=rank(H_0)/dim(V)>0.
```

Amplify by `C^N`, where `N` makes `hN dim(V)/rank(E_0)` integral, and put

```text
E=E_0 tensor I_N,       H=H_0 tensor I_N,       F=E-H.
```

Choose `q=E_0 tensor Q_N<=E` with `tr(q)=h`.  Since
`rank(E-q)=rank(F)`, choose a unitary `U` which maps `E-q` onto `F` and maps
`q` onto a projection `C<=1-E` of the same rank.  Complete these two
isometries arbitrarily on the orthogonal complements.  Then

```text
UEU^*=F+C=:Q,       F<=Q,       tr(C)=tr(H)=h,           (EMM2)
X=FUE,              X^*X=E-q.                           (EMM3)
```

All reset and type-vector relations are exact because their operators are
the amplification of the fixed label representation.  To include the
diagonal-difference incidence, tensor with the old-spin Toeplitz model and
use exactly the factorization from
`translation-reset-leaves-a-compressed-gram-spectator`,

```text
t=T tensor U,       U_chord=I tensor U,
c=t U_chord^(-1)=T tensor I.
```

Every addressed old-spin Pauli and shifted reset relation is then exact.

For every source-corner coefficient `a,b` one has

```text
aQb=aFb,
```

because `C<=1-E`.  Therefore every currently available inside-corner D8,
selector, Hecke, Reynolds, and mixed coefficient test takes exactly its
intended value.  Also the two range projections are nested, so their
reflections commute exactly.  This verifies the whole
completeness-preserving existing menu.

Finally `fanizza-full-reflection-row-has-sharp-mirror-floor`, applied to
`Q=F+C`, gives equality in its sharp bound:

```text
||R_F U R_E U^*-1||_2^2
 =4||Q-F||_2^2
 =4 tr(C)
 =4h.                                                   (EMM4)
```

Thus the selected oriented row is separated in an exact model of the menu.
Full-label chord normalization would detect this model, but it forces the
chord into a fixed-label normalizer and preserves the finite label rank
deficit in every infinite amplification.  By
`full-label-chord-normalization-kills-the-hilbert-hotel`, it is not an
admissible completeness-preserving addition to this route.  No existing
mixed chord--reset relation remains which can authenticate `(EMM4)`.
