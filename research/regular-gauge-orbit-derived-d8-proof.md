---
rg: 2
id: regular-gauge-orbit-derived-d8-proof
kind: route
title: Put the square D8 action on each four-point gauge coset
target: regular-gauge-orbit-contains-equal-scale-derived-d8-reset
requires:
  - gauge-doubling-gives-selector-flip-symmetries
---

Present the square dihedral group as

```text
D8=<r,f | r^4=f^2=1, f r f=r^(-1)>.
```

Its center is `z=r^2`.  The two elements

```text
p=f,
q=r f
```

are involutions.  Since `p q=f r f=r^(-1)`,

```text
[p,q]=(p q)^2=r^(-2)=r^2=z.
```

In the natural action on the four vertices of a square, `z` is a fixed-point
free involution, hence a product of two transpositions.  Translation by `s`
on each coset of `<s,t>` has the same cycle type.  A bijection of the two
paired orbits conjugates `z` to that translation.  Transport `p,q` through
this bijection and repeat the same construction independently on every coset.
This proves all relations in `(GOD1)` as literal permutation identities.

The character of the square permutation representation has dimension four.
The central half-turn has trace zero, so its two eigenspaces both have
dimension two.  Every one-dimensional representation of `D8` kills the
commutator `z`, hence has central sign `+1`.  The entire `z=-1` eigenspace is
therefore the unique two-dimensional spin simple.  Repeating over
`2^(m-2)` cosets proves `(GOD2)`.

Finally, gauge covariance gives

```text
Pi(X)=direct_sum_g pi(theta_g(X))=I_(C[Omega]) tensor pi(X)
```

for every gauge-invariant logical word `X`.  Every permutation of `Omega`, in
particular `p` and `q`, commutes with these operators.  The marked base and
signal are therefore preserved exactly.

