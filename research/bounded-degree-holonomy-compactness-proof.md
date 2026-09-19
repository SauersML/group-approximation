---
rg: 2
id: bounded-degree-holonomy-compactness-proof
kind: route
title: Compact each bounded block and discard the weighted high-defect tail
target: bounded-degree-holonomy-collapses-for-map-groups
requires: []
---

Fix `D`.  For `1<=m<=D` and a tuple

```text
x=(x_s)_(s in S) in U(m)^S
```

put

```text
e_m(x)=max_(r in R)||r(x)-1||_(2,m),
a_m(x)=max_(s in S)||x_s-1||_(2,m).
```

For every `eta>0` there is `theta_D(eta)>0` such that

```text
e_m(x)<theta_D(eta)  =>  a_m(x)<eta                 (BDP1)
```

simultaneously for all `m<=D`.  Otherwise there are `m_n<=D` and tuples
`x_n` with `e_(m_n)(x_n)->0` and `a_(m_n)(x_n)>=eta`.  Pass to a subsequence
with constant `m`.  Compactness of `U(m)^S` gives a limit `x`.  Every
relator is one at `x`, so `x` is a genuine `m`-dimensional representation
of `Gamma`.  It is trivial by hypothesis, contradicting `a_m(x)>=eta`.

Now write the finite-dimensional subhomogeneous algebra as

```text
A = direct_sum_(j in J) M_(m_j),       m_j<=D,
tau = sum_j lambda_j tr_(m_j),         sum_j lambda_j=1.
```

Let `x^(j)` be the tuple in the `j`th block and set

```text
E_j=max_(r in R)||r(x^(j))-1||_(2,m_j)^2.
```

Although the relator maximizing `E_j` may depend on `j`, finiteness of `R`
gives

```text
sum_j lambda_j E_j
 <= sum_(r in R)||r(u)-1||_2^2
 <= |R| delta^2.                                      (BDP2)
```

Fix `eta=epsilon/2` and put `theta=theta_D(eta)`.  Call a block bad when
`E_j>=theta^2`.  Markov's inequality and `(BDP2)` give

```text
mu_bad:=sum_(j bad)lambda_j <= |R|delta^2/theta^2.     (BDP3)
```

On every good block `(BDP1)` gives

```text
max_s||x_s^(j)-1||_(2,m_j)<epsilon/2.
```

On a bad block the distance between two unitaries is at most `2`.  Hence,
for every generator `s`,

```text
||u_s-1||_2^2
 =sum_j lambda_j||x_s^(j)-1||_(2,m_j)^2
 <=epsilon^2/4 + 4 mu_bad
 <=epsilon^2/4 + 4|R|delta^2/theta^2.                 (BDP4)
```

Choose

```text
delta < epsilon theta/(4 sqrt(|R|)).                  (BDP5)
```

Then the right side of `(BDP4)` is strictly below `epsilon^2/2`, proving
`(BDH1)` with room to spare.  The estimate never uses the number of blocks
or their multiplicities.

For the tight-degree extension, fix `zeta>0` and choose `D` as in `(BDH2)`.
Let `p_n` be the central sum of the blocks of degree at most `D`, and put
`b_n=1-tau_n(p_n)`.  Along the tail under consideration, `b_n<zeta` and
`tau_n(p_n)>1-zeta`.  In the normalized trace on `p_nA_np_n`, every fixed
relator's squared defect is at most its ambient squared defect divided by
`1-zeta`.  It therefore tends to zero.  The bounded-degree result makes
every compressed generator tend to the identity, while

```text
||(1-p_n)(u_s-1)||_2^2 <=4b_n.                         (BDP6)
```

First let `n` tend to infinity and then let `zeta` tend to zero.  This proves
collapse under `(BDH2)`.

Conversely, suppose along a subsequence one fixed generator satisfies
`||u_s-1||_2>=a`.  For each fixed `D`, the degree-at-most-`D` part collapses
by the same conditional argument whenever it has nonzero limiting mass.
The complementary part contributes at most four times its trace mass, so

```text
a^2 <=4 limsup_n mu_n({m>D}).                           (BDP7)
```

This is `(BDH3)` and proves that every surviving enemy has a quantitatively
non-tight block-degree distribution.

For the Kac--Moody specialization, infinite finite generation, simplicity,
and Malcev residual finiteness of finitely generated linear groups imply
that every finite-dimensional unitary representation is trivial.  Applying
the theorem to a hypothetical regular-core holonomy sequence proves the
stated unbounded-degree necessity.
