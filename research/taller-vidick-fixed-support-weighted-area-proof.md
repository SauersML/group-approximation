---
rg: 2
id: taller-vidick-fixed-support-weighted-area-proof
kind: route
title: Separate positive-noise support from weights and telescope a weighted certificate
target: taller-vidick-positive-noise-fixed-support-reweighting
requires:
  - taller-vidick-lcs-re-hardness
---

Definition 4.1 of Taller--Vidick,
*Approximating the quantum value of an LCS game is RE-hard*,
arXiv:2507.22444v2 (2026), samples `mu(y)` independently with probabilities
`1-epsilon` and `epsilon`, then sets `g'=fgmu`.  For `(TVF1)`, every mask has
positive probability.  Since multiplication by `fg` is a bijection on
`F_W`, `g'` determines `mu`; hence the possible equation tuples are
independent of positive `epsilon`.  Their construction of the LCS variables
and equations immediately after Proposition 4.1 uses precisely this finite
set of possible tuples.  Lemma 4.2 gives completeness `1-epsilon`.

Equations `(TVF3)--(TVF4)` follow termwise from

```text
kappa p_r<=q_r<=K p_r.
```

Taking the infimum of loss over strategies proves `(TVF5)`.  For the
completeness direction, apply the upper inequality to the particular honest
strategy.  The all-minus mask gives the stated inverse-weight growth.

For `(TVF7)`, evaluate `(TVF6)` on an arbitrary unitary tuple and telescope
the product.  Unitary invariance of normalized Hilbert--Schmidt norm gives

```text
||u(U)-1||_2 <= sum_r m_r ||r(U)-1||_2.
```

Weighted Cauchy--Schwarz gives

```text
(sum_r m_r d_r)^2
 <= (sum_r m_r^2/p_r)(sum_r p_r d_r^2),
d_r=||r(U)-1||_2,
```

which is `(TVF7)`.  If `u(U)=-1`, its distance from the identity is `2`,
giving `(TVF8)`.

Theorem 5.2, proof equation defining `s''`, chooses `u` to make `(TVF9)`
hold after fixing `epsilon`.  This verifies the final quantifier caveat:
the paper proves fixed support only conditional on fixed `u`, while its
RE-hard soundness reduction uses `u=u(epsilon)`.

