---
rg: 2
id: finite-normal-generator-hs-trivialization
kind: claim
title: A finite normal generator quantitatively forces unitary representations into their trivial sector
---

Let `G` be a finite group and let `g in G` normally generate `G`.  There is an
integer `L=L(G,g)<infinity` with the following dimension-free property.
For every finite-dimensional unitary representation

```text
pi : G -> U(d)
```

and the invariant-space projection

```text
Q_pi = (1/|G|) sum_(x in G) pi(x),
```

normalized Hilbert--Schmidt norm satisfies

```text
||1-Q_pi||_2 <= L ||pi(g)-1||_2,                       (NG-HS-1)
tr_d(1-Q_pi) <= L^2 ||pi(g)-1||_2^2.                   (NG-HS-2)
```

Thus for an arbitrary sequence of dimensions, if one fixed normal generator
acts `o(1)` from the identity then the total normalized dimension of every
nontrivial irreducible sector is `o(1)`.  No representation-theoretic constant
may deteriorate under external amplification.

## Attempts

- Choose finitely many conjugates of `g` generating `G`, use the finite Cayley
  diameter to telescope every `pi(x)-1`, and average.  The second inequality
  should then be the projection identity `||1-Q_pi||_2^2=tr_d(1-Q_pi)`.
