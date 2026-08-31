---
rg: 2
id: qutrit-rank-six-parity-bridge-proof
kind: route
title: Separate the stabilizer line from the parity line and close the weak gluing
target: qutrit-rank-six-parity-bridge-is-impossible-or-virtually-free
requires:
  - thompson-27-cylinder-qutrit-cell-is-fd-invisible
  - finite-projective-sector-groupoids-have-conjugate-absorbers
  - finite-support-corner-localizes-obstruction
---

In the spin representation, take

```text
Z_1=diag(1,omega,omega^2) tensor I_3.
```

The formula
`R=z_(C,chi_0)+z_(C,chi_1)` says exactly that the first qutrit has
`Z_1`-label `0` or `1`.  Therefore

```text
R=diag(1,1,0) tensor I_3
 =(1-|2><2|) tensor I_3,                                (QPB5)
```

which also reads its rank as `2*3=6`.

In the ordered basis `|0>,|1>,|2>`, parity and its positive cut are

```text
Pi = [[1,0,0],[0,0,1],[0,1,0]],

E_+ = [[1,0,0],
       [0,1/2,1/2],
       [0,1/2,1/2]].                                    (QPB6)
```

The negative line is spanned by

```text
|m>=(|1>-|2>)/sqrt(2),             1-E_+=|m><m|.        (QPB7)
```

Suppose `(QPB2)` held.  Taking complementary projections would give

```text
g|2><2|g^*=|m><m|.                                     (QPB8)
```

The vector `|2>` is a qutrit stabilizer state.  A Clifford maps stabilizer
states to stabilizer states because it normalizes the qutrit Pauli group.
But `|m>` is not a stabilizer state.  Indeed an eigenvector of a nontrivial
one-qutrit Pauli has either support one in the computational basis, when the
Pauli is a nontrivial power of `Z`, or support three with all three
coordinates of equal modulus, when its `X`-power is nonzero.  The vector
`|m>` has support exactly two.  This contradicts `(QPB8)` and proves the
Clifford impossibility.

A one-qutrit Clifford normalizer on the first tensor factor acts by
automorphisms of the finite Heisenberg packet.  Hence any actual Clifford
conjugate of `R` would merely permute its finite group-algebra support and
would preserve the coefficientwise three-phase cancellation.  The argument
above shows that no such cancellation-preserving conjugate is the parity
cut; rank equality alone does not supply the missing occurrence.

Now weaken the attachment to the central amalgam in `(QPB3)`.  Let
`pi_F` be the nine-dimensional spin representation of `F` and let
`pi_A` be the stated representation of `A).  Their restrictions to
`C` agree by scalar operators.  Since the positive cut of `pi_A(u)` and
`R` both have rank six, choose a unitary `W` with

```text
W (1+pi_A(u))/2 W^*=R.                                  (QPB9)
```

Every operator from `pi_A(C)` is scalar, so `W` commutes with it.
Consequently `Ad(W) o pi_A` still agrees with `pi_F` on `C`.  The
universal property of the amalgam gives a nine-dimensional representation

```text
rho:F *_C A -> U(9)                                     (QPB10)
```

whose restriction to `F` is the full spin packet and for which the
distinguished parity cut is exactly `R`.  Thus the qutrit context, its
three-phase marginal, and the parity identification all hold in one exact
finite-dimensional model.

Finally, an amalgam of finite groups over a finite subgroup is the
fundamental group of a finite graph of finite groups.  It is virtually free,
hence residually finite and hyperlinear.  Finite-support localization cannot
turn this support group into a nonhyperlinear endpoint.  This proves both
sides of the stated dichotomy.
