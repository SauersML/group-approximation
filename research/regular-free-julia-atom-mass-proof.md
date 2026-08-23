---
rg: 2
id: regular-free-julia-atom-mass-proof
kind: route
title: Compute each Julia atom by one regular group coefficient
target: regular-free-julia-atom-mass-is-uniform-or-affine
requires:
  - free-julia-grading-carries-one-gram-at-canonical-quarter-mass
---

Because `q_chi<=P_+`, cyclicity and `q_chi^2=q_chi` give

```text
||q_chi G||_2^2
 =tau(P_-j q_chi jP_-)
 =tau(q_chi jP_-j q_chi)
 =tau(q_chi jP_-j)
 =1/2[tau(q_chi)-tau(q_chi jzj)].                     (RFJP1)
```

The first term is `|D|^(-1)`.  For the second, put `a=jzj`.  Expanding the
Fourier atom,

```text
tau(q_chi a)
 =|D|^(-1) sum_(d in D) chi(d) tau(da).                (RFJP2)
```

The canonical group trace of `da` is nonzero exactly when `da=1`.  If
`a notin D`, no summand survives.  If `a in D`, the unique surviving term is
`d=a^(-1)=a`, and `(RFJP2)` equals `chi(a)/|D|`.  Substitution in `(RFJP1)`
proves `(RFJ4)`.

If `a in D`, characters with fixed value `chi(z)=+1` evaluate the nontrivial
class of `a` by a nonconstant affine parity unless `a=z`.  Hence the two
values occur on equal halves.  If `a=z`, then `jzj=z`, so `j` commutes with
`z`, `zjzj=1`, and `G=0` by `(FJG3)`.  This proves the dichotomy.

Finally, every defining relator has zero regular-representation energy.
Applying a proposed tracially functorial `(RFJ5)` therefore makes every
forbidden term in `(RFJ4)` zero.  The uniform case is impossible for a
nonempty forbidden set, and the affine case gives `(RFJ6)`.
