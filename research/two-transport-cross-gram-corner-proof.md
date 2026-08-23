---
rg: 2
id: two-transport-cross-gram-corner-proof
kind: route
title: Telescope the cross Gram and average its spectral cuts
target: two-transport-cross-gram-has-a-fixed-mass-reducing-corner
requires: []
---

Since the `A_s,B_s` are unitary and the rectangular `T_i` are contractions,

```text
B_s^*GB_s=(T_1B_s)^*(T_2B_s),
G=(A_sT_1)^*(A_sT_2).
```

One two-term telescoping and the rectangular Schatten inequality
`||XY||_(2,B)<=||X||_(2,B)||Y||_op` prove `(TCG2)`.
Put `K=B_s^*GB_s`.  Then `B_s^*HB_s=K^*K`, and

```text
||K^*K-G^*G||_2
 <=(||K||_op+||G||_op)||K-G||_2<=2||K-G||_2,
```

which proves `(TCG3)`.

For the cutoff, diagonalize `H` with eigenvalues `h_i in [0,1]` and write
`b_(ij)` for the matrix entries of one `B_s`.  If
`P_t=1_[t,1](H)`, then for every interval `I subset [0,1]`,

```text
integral_I ||[P_t,B_s]||_2^2 dt
 <=d^(-1) sum_(i,j)|h_i-h_j||b_(ij)|^2
 <=||[H,B_s]||_2.                                    (TCP1)
```

The first inequality holds because the set of thresholds separating two
numbers `h_i,h_j` has length at most `|h_i-h_j|`; the second is
Cauchy--Schwarz and `d^(-1)sum_(i,j)|b_(ij)|^2=1`.
Use `(TCG3)`, sum `(TCP1)` over `s`, and take
`I=[m/4,m/2]`, whose length is `m/4`.  Some `t in I` then obeys the second
inequality in `(TCG5)`.  If `p=tau(P_t)`, positivity and `H<=1` give

```text
m=tau(H)<=t(1-p)+p,
p>=(m-t)/(1-t)>=m/2,                                  (TCP2)
```

proving the mass bound.  Cauchy--Schwarz over `s` gives `(TCG6)`.

Finally let `E` be conditional expectation onto `{B_s:s in S}'`.  By
`(TCG7)` and `(TCG5)`,

```text
||P-E(P)||_2<=kappa^(-1)sqrt(8D/m).                   (TCP3)
```

The projection `P_0=1_[1/2,1](E(P))` lies in the commutant.  Spectral
rounding minimizes Hilbert--Schmidt distance from the positive contraction
`E(P)` to a projection, so

```text
||P-P_0||_2<=2||P-E(P)||_2.
```

Together with `|tau(P)-tau(P_0)|<=||P-P_0||_2`, this proves
`(TCG8)--(TCG9)`.
