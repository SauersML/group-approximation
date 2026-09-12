---
rg: 2
id: stw99-xciv-local-norm-central-z-equivalence-proof
kind: route
title: Recursively absorb each newly adjoined Z copy into the next finite test
target: stw99-xciv-separable-zstability-iff-local-norm-central-z
requires: []
---

We use the standard strongly-self-absorbing absorption criterion in exactly
two places: for a separable unital `C`,

```text
C ~= C tensor Z
```

if and only if there is a unital homomorphism
`Z -> C_infinity intersect C'`.  In the forward direction the homomorphism
may be represented, for any prescribed finite tests, by actual unital
homomorphisms `Z->C` which are approximately central.  This criterion is the
only external absorption input.

Suppose first that condition 1 holds.  Given `F,G,epsilon`, choose a separable
unital `Z`-stable subalgebra `C subset B` containing `F`.  The forward part of
the absorption criterion supplies a unital `phi:Z->C` satisfying the required
finite commutator estimates.

Conversely, assume condition 2 and fix a norm-separable `S subset B`.  Set
`C_0=C*(S,1)`.  Recursively, after constructing a separable unital `C_n`,
choose a countable dense set `D_n` in its unit ball.  At stage `n`, make a
finite test set containing the first `n` elements of each

```text
D_0,D_1,...,D_n
```

and the first `n` elements of a fixed dense sequence in the unit ball of
`Z`.  Condition 2 gives a unital homomorphism `phi_n:Z->B` whose commutators
on these tests are less than `1/n`.  Put

```text
C_{n+1}=C*(C_n,phi_n(Z)),
C=closure(union_n C_n).
```

The algebra `C` is separable, unital, and contains `S`.  The coordinatewise
map

```text
Phi:Z -> C_infinity,       Phi(z)=[(phi_n(z))_n]
```

is a unital homomorphism because every `phi_n` is one.  The diagonal choice
of tests shows that `Phi(Z)` commutes with every dense-set element from every
`C_m`, hence with all of `C`.  Thus

```text
Phi:Z -> C_infinity intersect C'
```

is unital.  The reverse part of the absorption criterion gives
`C ~= C tensor Z`, proving condition 1.

Notice why the newly adjoined ranges are included in later tests: merely
centralizing the original `S` would not prove that the generated hull itself
is `Z`-stable.
