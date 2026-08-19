---
rg: 2
id: s3-weighted-two-generator-covariance-controls-commutant-distance-proof
kind: route
title: Diagonalize the weighted S3 Cayley Laplacian and polar-round the expectation
target: s3-weighted-two-generator-covariance-controls-commutant-distance
requires: []
---

On the Hilbert--Schmidt space put

```text
alpha(g)(T)=rho(g)T rho(g)^*,
E=(1/6)sum_(g in S3)alpha(g),
Delta_(p,q)=p(I-alpha(s))+q(I-alpha(t)).
```

The trivial representation has eigenvalue `0`, while the sign representation
has eigenvalue `2(p+q)`.  In the standard two-dimensional representation choose
reflection axes meeting at angle `pi/3`.  Then `p alpha(s)+q alpha(t)` has
eigenvalues

```text
+-sqrt(p^2-pq+q^2),
```

so the two weighted-Laplacian eigenvalues are

```text
p+q +- sqrt(p^2-pq+q^2).
```

Hence on the orthogonal complement of the invariant space,

```text
Delta_(p,q) >= lambda(p,q)(I-E),

lambda(p,q)=p+q-sqrt(p^2-pq+q^2).
```

For unitary `U`,

```text
p a^2+q b^2
 =2 <U,Delta_(p,q)U>
 >=2 lambda(p,q)||U-E(U)||_2^2.                        (1)
```

Set `X=E(U)`.  As in the symmetric theorem, `X` is a contraction in the
commutant.  Polar-decompose it there and extend the polar partial isometry to a
commuting unitary `V`.  Orthogonality of `E` and `0<=|X|<=1` give

```text
||U-V||_2^2 <=2||U-X||_2^2.                            (2)
```

Combining `(1)` and `(2)` yields

```text
lambda(p,q)||U-V||_2^2 <= p a^2+q b^2.
```

Infimizing over commuting unitaries proves `(S3-WCOV)`.  No representation
multiplicity enters the spectrum, so the constant is dimension-free.