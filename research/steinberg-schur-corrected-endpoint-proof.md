---
rg: 2
id: steinberg-schur-corrected-endpoint-proof
kind: route
title: Apply Pascal inversion and isolate the corrected endpoint derivative
target: steinberg-schur-corrected-endpoint-reduction
requires: []
---

Expanding the four terms of `(SCE1)` gives the dense coefficient
`binom(j+v-1,j)-1_(v>=j)binom(v,j)` and, when `j+v=p`, the correction
`(-1)^j(2^(2j-1)-1)`.  This is exactly `(SRP7)`.  The only coefficient above
the tested range is `(SCE2)`, proving `(SCE3)`.

For the endpoint form, multiply by the explicit Pascal inverse `(SCE5)`.
The full finite-difference sum is `binom(j-1,v-1)`; removing its omitted
degree-one term subtracts `(-1)^(v-1)v`, giving the first identity in
`(SCE6)`.  The antidiagonal has one contributing index and gives the second.
Row two of `R` vanishes, so `Rq=1(c^Tq)` implies `c^Tq=0` and then `Rq=0`;
this proves `(SCE8)--(SCE10)`.  Translation by the Pascal matrix gives
`(SCE11)`.  Finally the single Jordan chain of `L-I` yields `(SCE12)` by the
rank-one determinant expansion and Wilson's theorem.
