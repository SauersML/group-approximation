---
rg: 2
id: sharply-two-transitive-lamp-fd-invisibility-proof
kind: route
title: Simple sharply 2-transitive actors make every finite-dimensional representation kill augmentation lamps
target: sharply-two-transitive-augmentation-lamp-host-audit
requires: []
---

Let `A`, `X`, `M`, and `Gamma` be as in
`sharply-two-transitive-augmentation-lamp-host-audit`.

First, an infinite finitely generated simple group has no nontrivial
finite-dimensional unitary representation.  Indeed, a finitely generated
linear group is residually finite.  A nontrivial representation of the
simple group `A` would be injective, making `A` residually finite.  A
nontrivial finite quotient of an infinite simple group would again be
injective, which is impossible.  Hence every such representation is
trivial.

Now let

```text
rho: Gamma -> U(d)
```

be a representation.  Its restriction to `A` is trivial.  Covariance then
makes the images of all pair lamps `m_xy=delta_x+delta_y` equal, because
`A` is transitive on ordered pairs of distinct points.  Write their common
image as `B`.  For three distinct points,

```text
m_xy + m_yz = m_xz,
```

so multiplicatively

```text
B B = B.
```

Since `B` is unitary, `B=I`.  Pair lamps span `M`; therefore `rho(M)=1`.

Equivalently on the Fourier side, any finite spectral support in `M_hat`
is a finite `A`-invariant set.  Simplicity rules out a nontrivial finite
permutation quotient, so every supported character is fixed by `A`.
An invariant linear functional on `M` is constant, say `c`, on all pair
lamps.  The same triangle identity gives `c+c=c` in `F_2`, hence `c=0`.
Thus the trivial character is the only finite-orbit character.

Finally let `S` be a finite Kazhdan generating set for `A`.  Every
nontrivial character orbit is infinite, so its quasi-regular
representation on `ell^2(A chi)` has no invariant vector.  The Kazhdan
constant for `(A,S)` therefore gives one spectral-gap lower bound,
independent of the orbit.  This is the exact uniform Schreier expansion
needed by the one-seed character argument.
