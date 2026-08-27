---
rg: 2
id: multiplicity-only-fanizza-row-mirror-proof
kind: route
title: Install the equal-rank complement swap after the finite-coordinate block has been selected
target: multiplicity-only-fanizza-row-selection-leaves-a-mirror
requires:
  - existing-fanizza-mixed-menu-leaves-balanced-mirror-exit
  - finite-packet-functoriality-has-positive-regular-profile
  - fanizza-full-reflection-row-has-sharp-mirror-floor
---

Fix the exact finite packet representation and let the decoder make its
arbitrary choice of `Z`.  The choice depends only on packet multiplicities,
so it is unchanged by the subsequent choice of the chord on the scalar
multiplicity coordinate.  By `(MRS1)`, choose

```text
C_Z<=(1-E)Z,             rank(C_Z)=rank(HZ).            (MRS3)
```

On `Z` define a symmetry `U_Z` which fixes `FZ`, swaps `HZ` with `C_Z`, and
is arbitrary on the remaining orthogonal complement.  Extend it by any
exact permitted chord on `1-Z`.  Then

```text
U_Z(EZ)U_Z^*=FZ+C_Z,       FZ<=U_Z(EZ)U_Z^*,            (MRS4)
FZ U_Z EZ=FZ,              (FZ U_Z EZ)^*(FZ U_Z EZ)=FZ.
                                                                  (MRS5)
```

Thus the selected source Gram has deficiency exactly `HZ`.

All fixed packet, reset, restriction, central-cut, and integer-flow data are
unchanged: they involve the label action and its multiplicities, not the
new scalar-coordinate swap.  The existing diagonal-difference incidence is
also exact after the standard tensor factorization

```text
t=T tensor U_Z,       U_chord=I tensor U_Z,
t U_chord^(-1)=T tensor I.
```

Every source-corner coefficient test is blind to `C_Z`, since
`C_Z<=(1-E)Z`; and the two selected range reflections commute because the
range projections in `(MRS4)` are nested.  Hence all current
completeness-preserving relations remain exact after the selector has made
its choice.

Apply the sharp reflection identity on `Z`.  Equation `(MRS4)` is its
equality case, so

```text
||Z(R_F U R_E U^*-1)||_2^2
 =4||C_Z||_2^2
 =4 tr(HZ).                                             (MRS6)
```

If the selector retains guard density
`tr(HZ)/tr(Z)>=c>0`, the conditional selected-row defect is at least
`2 sqrt(c)` independently of dimension.  Since the construction is made
after the multiplicity rule announces `Z`, no selector-only refinement can
avoid it.  Excluding `(MRS3)--(MRS6)` requires a new chord-sensitive
relation on the selected multiplicity block.
