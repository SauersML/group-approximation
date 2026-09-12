---
rg: 2
id: tensor-powers-upgrade-one-cutoff-to-radical
kind: route
title: Tensor powers upgrade one cutoff below sqrt(2) to exact word death
target: hyperlinear-radical-is-finitely-witnessed
requires:
  - hyperlinear-radical-presentation-compactness
---

Suppose `w in Rad_hyp(Gamma)`. Apply
`hyperlinear-radical-presentation-compactness` once, at a fixed
`alpha<sqrt(2)`, to obtain `N,delta` such that small defect on the first `N`
relators forces `||w(U)-I||_2<alpha`.

Let `theta:Gamma_N->prod_omega U(d_n)` be any homomorphism, represented on the
generators by tuples `U_n`, and put `V=theta(w)`. For every fixed `k`, the
tensor-power tuples `U_n^(tensor k)` still satisfy the first `N` relators
asymptotically, so

```text
||V^(tensor k)-I||_2<=alpha.
```

Writing `z=tau_omega(V)`, this says

```text
2-2 Re(z^k)<=alpha^2,
Re(z^k)>=1-alpha^2/2>0                                  (HRF2)
```

for every `k`. If `|z|<1`, the left side tends to zero, contradicting the
positive lower bound. Hence `|z|=1`; equality in Cauchy--Schwarz for the
unitary `V` gives `V=zI`. If `z!=1`, the Cesaro means of `z^k` tend to zero,
again contradicting `(HRF2)`. Thus `V=I`, and `w in Rad_hyp(Gamma_N)`.

Conversely, `Gamma` is a quotient of `Gamma_N`, so radical membership in
`Gamma_N` implies radical membership in `Gamma`.
