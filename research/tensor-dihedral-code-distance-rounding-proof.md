---
rg: 2
id: tensor-dihedral-code-distance-rounding-proof
kind: route
title: Align each dihedral factor and charge it through a positive-density partner codeword
target: tensor-dihedral-soft-modes-round-by-code-distance
requires: []
---

On every factor replace `T_t` by `S`.  Thus

```text
q_i'^(t)=S^(c_t(i)+d_t(i)),       Q_i'=tensor_t q_i'^(t). (TDP1)
```

All `Q_i'` commute.  Since `c_t+d_t` is a codeword, every parity face
contains an even number of `S` factors for each `t`; hence its product is
`I`.  The original tuple also satisfies every face exactly: by face
separation, a fixed factor contributes only copies of `S`, only copies of
`T_t`, or identities, and the relevant codeword has even face parity.

Use normalized trace on every tensor factor.  Put

```text
v_t=-log(cos(2theta_t)),
u_t=-log(cos(4theta_t)).                                 (TDP2)
```

Both numbers are nonnegative and `u_t>=v_t`.  For a fixed coordinate `i`,
only the factors with `d_t(i)=1` change, and multiplicativity of tensor
trace gives

```text
||Q_i-Q_i'||_2^2
 =2(1-exp(-sum_(t:d_t(i)=1)v_t)).                        (TDP3)
```

For a pair `(i,j)`, a factor contributes `cos(4theta_t)` to

```text
Re tau((Q_iQ_j)^*(Q_jQ_i))
```

exactly when one coordinate lies in `supp(c_t)` and the other lies in
`supp(d_t)`; every other contribution is one.  All factors are nonnegative
because `theta_t<pi/8`.  In particular, after retaining only the crossings
with `d_t(i)c_t(j)=1`,

```text
||[Q_i,Q_j]||_2^2
 >=2(1-exp(-sum_(t:d_t(i)=1)u_t c_t(j))).                (TDP4)
```

We use the following elementary correlated-indicator inequality.  If
`w_t>=0`, `z_t(j) in {0,1}`, and `E_j z_t(j)>=delta` for every `t`, then

```text
E_j[1-exp(-sum_t w_t z_t(j))]
 >=delta(1-exp(-sum_t w_t)).                             (TDP5)
```

Indeed, for `0<=x<=W=sum_t w_t`, concavity and the zero endpoint give
`1-exp(-x)>=(x/W)(1-exp(-W))`; average and use
`E_j sum_t w_tz_t(j)>=delta W`.  No independence of the indicators is
needed.

For every active `t`, the nonzero codeword `c_t` has weight at least
`delta L`.  Apply `(TDP5)` to `(TDP4)`, with
`w_t=u_t 1_(d_t(i)=1)`, and then use `u_t>=v_t`.  Equations
`(TDP3)`--`(TDP5)` give, for every `i`,

```text
(1/L)sum_j||[Q_i,Q_j]||_2^2
 >=delta ||Q_i-Q_i'||_2^2.                              (TDP6)
```

Average `(TDP6)` over `i` to obtain `(TDS3)`.  Angles equal to `pi/8` follow
by a limit if desired; the strict range avoids extended-real notation in
`(TDP2)`.
