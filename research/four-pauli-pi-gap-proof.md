---
rg: 2
id: four-pauli-pi-gap-proof
kind: route
title: Compare the standard polynomial on two Pauli pairs and one degree-two factor
target: four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
requires: []
---

For the alternating degree-four polynomial `s4`, reorder its 24 monomials to
`ABCD`.  Under two anticommutation and four cross-commutation relations the
signed terms sum to `8ABCD`.  At most six adjacent swaps are needed per
monomial; if every relation error is at most `epsilon`, unitary invariance
gives

```text
||s4(A,B,C,D)||_2>=8-24*6 epsilon.
```

If all four operators are within `delta` of one unital `M_2` factor, choose
contraction approximants there.  Amitsur--Levitzki makes `s4` vanish on that
factor, while multilinearity changes each of 24 degree-four monomials by at
most `4 delta`.  Therefore `||s4||_2<=96 delta`.  Combining yields
`144 epsilon+96 delta>=8`, and setting both errors to `eta` gives
`eta>=1/30`.  Normalized HS norms and both estimates are unchanged by
tensoring spectators, proving amplification blindness.
