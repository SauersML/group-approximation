---
rg: 2
id: mihailova-sl3-coset-amplification-proof
kind: route
title: Compute the fibers and vertical stabilizers of the mixed coset set
target: mihailova-sl3-restriction-is-coset-amplification
requires: []
---

Right multiplication by `(u,v) in P` changes the first coordinate `gamma`
to `gamma u`, so `(MSR2)` is well-defined.  Left multiplication by
`{e} times L` does not change the first coordinate, hence every `L`-orbit is
contained in a fiber.

Conversely, suppose `(gamma,l)P` and `(gamma u,l')P` lie in the same fiber,
with `u in F`.  Surjectivity of `pi_2` gives `v in E` such that
`pi_2(v)=pi_1(u)`, so `(u,v) in P`.  Then

```text
(gamma u,l')P=(gamma,l'v^(-1))(u,v)P
              =(gamma,l'v^(-1))P,
```

which is in the `L`-orbit of `(gamma,l)P`.  Thus each fiber is exactly one
orbit.

The stabilizer in `L` of `(gamma,l)P` consists of the `s in L` for which

```text
(gamma,l)^(-1)(e,s)(gamma,l)=(e,l^(-1)s l) in P.
```

An element of `P` with first coordinate `e` has second coordinate precisely
in `N=ker(pi_2)`.  Hence the stabilizer is `l N l^(-1)`, and its transitive
orbit is isomorphic to `L/N`.  This proves `(MSR3)`.  Taking free binary
permutation modules gives `(MSR4)`, and Pontryagin duality gives `(MSR5)`.
