---
rg: 2
id: periodic-clock-fourth-power-escape-proof
kind: route
title: Put a sine window on the short power-of-two segment
target: periodic-clock-has-opnorm-almost-central-fourth-power-escape
requires: []
---

Put `m=floor(n/2)` and `theta=pi/(m+2)`.  For `0<=j<=m`, let

```text
a_j=sqrt(2/(m+2)) sin((j+1)theta),
v_n=sum_(j=0)^m a_j e_(2^j).                         (1)
```

The powers `2^j` in `(1)` are distinct residues because `2^m<3^n`.
The sine normalization identity gives `||v_n||=1`.

For `j>=1`, multiplication by `2^(-1)` sends `2^j` to `2^(j-1)`.
The image of `1` is `(q_n+1)/2`, outside the displayed segment for all
sufficiently large `n`.  Extending the coefficient sequence by
`a_(-1)=a_(m+1)=0`, the standard first Dirichlet eigenvector calculation
therefore gives

```text
||P_n v_n-v_n||^2
 =sum_(j=-1)^m |a_(j+1)-a_j|^2
 =2-2cos(theta)
 <=theta^2.                                          (2)
```

On the support of `v_n`, the argument of the diagonal clock is at most
`2 pi 2^m/3^n`.  Hence

```text
||D_n v_n-v_n|| <=2 pi 2^m/3^n.                     (3)
```

Both right sides tend to zero.

Let `E_n` be the rank-one projection onto `C v_n`, and set

```text
C_n=1-2E_n,
R_n=1+(exp(pi i/4)-1)E_n.                            (4)
```

Then `R_n` is unitary and `R_n^4=C_n`.  For any unitary `U`,

```text
||[E_n,U]||
 =||E_n-U E_n U^*||
 <=||v_n-Uv_n||.                                     (5)
```

Equations `(2)--(5)` prove `(ACE2)`.

Finally `v_n` is supported on the orbit of the units modulo `3^n` under
multiplication by `2`.  By the exact joint-commutant calculation in
`higman-fourth-return-jointly-centralizes-clock-proof`, every
`Z in {P_n,D_n}'` restricts to a scalar `lambda` on that whole orbit
subspace.  The restriction of `C_n` has eigenvalue `-1` on `v_n` and
eigenvalue `1` on its orthogonal complement.  Therefore

```text
||C_n-Z||
 >=max(|1-lambda|,|-1-lambda|)
 >=1.                                                (6)
```

Taking the infimum over `Z` proves `(ACE3)`.

All operators used above reduce the unit-shell subspace.  Restricting to it
makes the joint commutant scalar because multiplication by `2` is transitive
on the units.  The same computation therefore proves the strengthened
primitive-shell statement in the claim.
