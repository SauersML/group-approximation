---
rg: 2
id: s3-two-generator-covariance-controls-commutant-distance-proof
kind: route
title: The S3 Cayley gap plus polar rounding gives the unitary commutant bound
target: s3-two-generator-covariance-controls-commutant-distance
requires: []
---

Let

```text
alpha(g)(T)=rho(g) T rho(g)^*
```

on the normalized Hilbert--Schmidt Hilbert space `M_d(C)`, and let

```text
E=(1/6) sum_(g in S3) alpha(g)
```

be the orthogonal projection onto `rho(S_3)'`.  Put

```text
Delta=2I-alpha(s)-alpha(t).
```

Because `s,t` are involutions, `alpha(s),alpha(t)` are self-adjoint unitaries.
On the three irreducible representations of `S_3`, the spectrum of `Delta` is

```text
trivial:   {0},
sign:      {4},
standard:  {1,3}.
```

Hence, in every unitary representation of `S_3`,

```text
Delta >= I-E.                                          (1)
```

For a unitary `U`, the two covariance defects are exactly the two edge
displacements for this Cayley graph, so

```text
a^2+b^2
 = ||U-alpha(s)U||_2^2+||U-alpha(t)U||_2^2
 = 2 <U,Delta U>
 >= 2 ||U-E(U)||_2^2.                                 (2)
```

It remains only to round the linear commutant point `X=E(U)` to a commuting
unitary.  Since `E` is an average of unitary conjugations, `||X||<=1` in
operator norm.  Take the polar decomposition of `X` inside the finite-
dimensional commutant and extend its polar partial isometry blockwise to a
unitary `V in rho(S_3)'`.  Orthogonality of the expectation gives

```text
||U-X||_2^2 = 1-||X||_2^2.
```

Moreover

```text
Re tr(U^*V)=Re tr(E(U^*)V)=tr(|X|) >= tr(|X|^2)=||X||_2^2,
```

where the inequality uses `0<=|X|<=1`.  Therefore

```text
||U-V||_2^2
 = 2-2 Re tr(U^*V)
 <= 2(1-||X||_2^2)
 = 2||U-X||_2^2
 <= a^2+b^2
```

by `(2)`.  Infimizing over commuting unitaries proves `(S3-COV)`.
