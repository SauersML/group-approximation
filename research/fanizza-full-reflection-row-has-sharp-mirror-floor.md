---
rg: 2
id: fanizza-full-reflection-row-has-sharp-mirror-floor
kind: claim
title: The full Fanizza reflection row has a sharp floor attained only by the balanced mirror exit
distinct_from:
  fanizza-compressed-unitary-has-guarded-rank-floor: that bounds the Hilbert--Schmidt Gram defect by rank-nullity; this gives an exact trace identity for the full reflection-conjugacy word and classifies its extremizers.
  toeplitz-range-commutator-has-a-balanced-mirror-exit: that proves the weaker commuting-reflection word is exactly blind to the mirror exit; this proves the full conjugacy word sees it with the smallest possible nonzero cost.
  unitary-offdiagonal-block-gram-is-support-leakage: that upper-bounds the Gram defect by an authenticated reflection row; this computes the reverse finite-rank ledger specific to a guarded target of smaller rank.
---

Let `H<=E` be projections in `M_d(C)`, put `F=E-H`, let `U` be unitary,
and define

```text
X=FUE,       Q=UEU^*,       R_E=1-2E,       R_F=1-2F,
h=tr_d(H),   ell=tr_d(E-X^*X).
```

Then exactly

```text
||R_F U R_E U^*-I||_2^2=8 ell-4h,                         (FRF1)
ell=h+||(1-Q)F||_2^2 >=h.                                 (FRF2)
```

Consequently

```text
||R_F U R_E U^*-I||_2^2 >=4h.                            (FRF3)
```

Equality holds precisely when `F<=Q`.  In that case

```text
Q=F+C,       C<=1-F,       tr_d(C)=h,                     (FRF4)
```

so the extremizer is exactly the balanced finite mirror exit.  Thus the
natural commuting-range word can have zero defect on the mirror model, but
the full oriented reflection-conjugacy row cannot: it charges the mirror by
the sharp amount `2 sqrt(h)`.

For the native Fanizza guard `h=1/8+o(1)`, any matrix-coordinate route which
authenticates the full selected row obtains a fixed defect floor
`1/sqrt(2)-o(1)`.  This is a useful exact reduction of the open compression
lemma, but it also locates the remaining burden: the row must be selected
only after finite-coordinate packet decoding.  If
`R_F U R_E U^*=I` were a literal group relation between fixed group-algebra
projections, the canonical regular trace would force `h=0` and destroy the
marked guard.  Raw packet multiplicities or the two range reflections alone
do not authenticate the selected oriented row.
