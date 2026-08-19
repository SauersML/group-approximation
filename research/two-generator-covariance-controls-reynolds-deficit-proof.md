---
rg: 2
id: two-generator-covariance-controls-reynolds-deficit-proof
kind: route
title: Subtract the Reynolds projection and commute the remainder
target: two-generator-covariance-controls-reynolds-deficit
requires: []
---

Write

```text
C=E_K(U),
X=U-C.
```

Since `C` lies in `rho(K)'`, it commutes with both `rho(a)` and `rho(b)`.
Unitary invariance therefore gives

```text
A = ||U rho(a)-rho(a)U||_2
  = ||X rho(a)-rho(a)X||_2
  <= ||X rho(a)||_2+||rho(a)X||_2
  = 2||X||_2,
```

and identically `B<=2||X||_2`.  Hence

```text
A^2+B^2 <= 8||U-E_K(U)||_2^2.
```

Finally `E_K` is the Hilbert--Schmidt orthogonal projection onto the finite
group commutant.  Pythagoras and `||U||_2=1` give

```text
||U-E_K(U)||_2^2 = ||U||_2^2-||E_K(U)||_2^2
                  = 1-||E_K(U)||_2^2.
```

This proves `(TCR)` with no loss depending on the group order or external
multiplicity.
