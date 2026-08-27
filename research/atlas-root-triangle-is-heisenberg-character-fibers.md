---
rg: 2
id: atlas-root-triangle-is-heisenberg-character-fibers
kind: claim
title: The first three rank-five root families reduce to Heisenberg character fibers
distinct_from:
  atlas-first-root-relator-is-half-block-commutant-face: that uses one commutator to make one transported root word block diagonal across one fixed involution; this intersects the neighboring same-source and same-target relations and identifies the resulting nonabelian finite commutant and its central-character fibers.
  atlas-three-label-mode-two-unitary-moment-reduction: that leaves two arbitrary coefficient unitaries and thousands of scalar moment equations; this replaces the first local subsystem by a fixed D8 Fourier decomposition plus finitely many multiplicity operators.
---

**ESTABLISHED EXACT LOCAL NORMAL FORM.**  For
`a in {1,e,f,E,F}`, write

```text
C_a = pi(x_12(a)),   X_a = pi(x_15(a)),
Y_a = pi(x_52(a)).                                     (HTF1)
```

The coefficient-one words are fixed first-chart transvections

```text
Z=C_1=lambda(I+E_34),
X=X_1=lambda(I+E_32),
Y=Y_1=lambda(I+E_24).                                  (HTF2)
```

They satisfy

```text
X^2=Y^2=Z^2=1,    [X,Y]=Z,    [X,Z]=[Y,Z]=1,           (HTF3)
```

so `H=<X,Y>` is the order-eight unitriangular group `UT_3(F_2)`, equivalently
`D8`.

The root-subgroup, same-source, same-target, Steinberg-product, and
involutivity entries of the literal packet imply

```text
C_a^2=X_a^2=Y_a^2=1,
[C_a,C_b]=1,
[C_a,X_b]=[C_a,Y_b]=1,                                 (HTF4)
[X_a,Y]=C_a,       [X,Y_a]=C_a.                        (HTF5)
```

Thus every `C_a` lies in the commutant of the same fixed nonabelian group
`H`, and the five `C_a` form one commuting family of involutions there.  Put

```text
Q_chi = 2^(-5) product_a (I+chi_a C_a),
chi in {+1,-1}^{ {1,e,f,E,F} }.                        (HTF6)
```

After deleting zero atoms, the `Q_chi` form the exact common reducing
decomposition forced by this root triangle.  Each `X_a,Y_a` preserves every
atom, and on `Q_chi H` the two simplest Steinberg rows become scalar
projective commutation laws

```text
[X_a,Y] Q_chi = chi_a Q_chi,
[X,Y_a] Q_chi = chi_a Q_chi.                           (HTF7)
```

In particular a negative sign is a Pauli/Clifford fiber, not a commuting
one.

The ambient size of the remaining variables is explicit.  If the coefficient
multiplicity is `r` and `m=2520 r`, then restriction of the regular `A8`
label to `H` gives

```text
l2(A8) tensor C^r = l2(H) tensor C^m,
{lambda(H) tensor I_r}'
  ~= M_m^4 direct-sum M_(2m).                          (HTF8)
```

The fixed bit `chi_1` separates these summands: `chi_1=+1` lies in the four
one-dimensional Fourier types of `D8`, whereas `chi_1=-1` lies in its unique
two-dimensional type.  Both halves have ambient normalized trace `1/2`.

This does **not** collapse the two coefficient unitaries to a commutative
algebra.  The local relations themselves retain full matrix multiplicity
blocks in `(HTF8)`, and their negative central-character fibers explicitly
carry Pauli pairs by `(HTF7)`.  What remains after the first root triangle is
therefore not an arbitrary pair of global moments: it is the collection of
matrix restrictions of the neighboring root words to the nonzero `Q_chi`,
subject to the scalar signs `(HTF7)`.  Relations involving further roots must
couple or eliminate these character fibers to obtain a contradiction.

For an asymptotically vanishing packet the same statement holds in the
tracial ultraproduct.  Equivalently, on matrix representatives the finite
commuting-involution family may be changed by `o(1)` in normalized
Hilbert--Schmidt norm to its joint spectral decomposition, while averaging
over the fixed eight-element `H` places the central family in `(HTF8)`.

DERIVATION
atlas-root-triangle-heisenberg-proof
