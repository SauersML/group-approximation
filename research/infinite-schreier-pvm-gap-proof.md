---
rg: 2
id: infinite-schreier-pvm-gap-proof
kind: route
title: Apply the bottom spectral gap to square roots of spectral ranks
target: infinite-schreier-pvm-transport-kills-finite-mark
requires: []
---

Put `p_v=tr_d(P_v)` and `f(v)=sqrt(p_v)`.  The support of `f` is finite.
For projections `P,Q` and a unitary `W`, normalized-trace
Cauchy--Schwarz gives

```text
||W P W^*-Q||_2^2
 >=(sqrt(tr_d(P))-sqrt(tr_d(Q)))^2.                           (1)
```

Sum `(1)` over the oriented colored edges in `(ISP2)`.  Symmetry gives

```text
E_PVM
 >=(1/D) sum_s sum_v |f(v)-f(sv)|^2
 =2 <f,(1-A)f>.                                               (2)
```

Apply `(ISP1)` and use `||f||_2^2=sum_v p_v=mu`.  This yields `(ISP3)`.

For the D8 consequence, let `P` be the marked projection and let one marked
involution `X` have spectral PVM supported by the trivial character together
with the expanding nontrivial orbits.  If a marked unitary `Z` satisfies
`ZXZ^*=-X` up to error `eta`, the trace calculation in
`one-seed-character-expansion-proof` puts at least

```text
tr_d(P)/2-sqrt(tr_d(P)) eta/4
```

in the nontrivial character PVM.  Combining this with `(ISP3)` and Young's
inequality collapses `tr_d(P)` in terms of actor energy and `eta^2`.
