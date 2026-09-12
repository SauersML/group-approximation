---
rg: 2
id: dual-singer-three-bit-incidence-fence-proof
kind: route
title: Classify dual Singer cross tables on one three-bit Pauli register
target: dual-singer-three-bit-incidence-retains-central-return
requires:
  - native-inverse-pair-seven-orbits-retain-external-gauge
---

Let `V=F_2^3`.  If `S in GL(V)` has order seven, then no nonidentity power
of `S` fixes a nonzero vector.  Indeed, the stabilizer of a fixed nonzero
vector maps to `GL_2(F_2)`, of order six, and the kernel of that map is a
two-group.  Hence that stabilizer has no element of order seven.  Every
nonzero `S`-orbit therefore has length seven and is exactly `V\{0}`.  The
same argument applies to `S^(-transpose)` on `V^*`.

The sum of all seven nonzero vectors of `F_2^3` is zero, since each
coordinate equals one four times.  Consequently, for every nonzero `a,phi`,

```text
sum_(k=0)^6 S^k a=0,
sum_(k=0)^6 S^(-transpose k)phi=0.                    (1)
```

For fixed `k`, the row

```text
(<S^(-transpose l)phi,S^k a>)_(l=0)^6                (2)
```

evaluates a nonzero vector against all seven nonzero functionals.  Exactly
four of those functionals take value one.  Dually every column also has
weight four.  Hence the complete table has weight `7*4=28`.  Replacing `S`
by any second Singer element changes only the order in which the same seven
vectors and functionals occur.

For the exact countermodel, fix nonzero `a,phi` with `<phi,a>=1`.  On
`C[V]` define

```text
X_a delta_x=delta_(x+a),
Z_phi delta_x=(-1)^<phi,x>delta_x,
U_S delta_x=delta_(Sx).                               (3)
```

Then

```text
U_S X_a U_S^(-1)=X_(Sa),
U_S Z_phi U_S^(-1)=Z_(S^(-transpose)phi),
[X_a,Z_phi]=(-1)^<phi,a>=-1.                         (4)
```

Equation `(1)` makes both ordered orbit products of the `X` occurrences
and both ordered orbit products of the `Z` occurrences equal to one.  The
operators within either family commute, so forward and reverse products
agree.  Equations `(2)` and `(4)` give the full cross table.

Take the direct sum of a trivial block and this Pauli block.  The central
scalar in `(4)` becomes the reflection

```text
E=1 direct_sum (-1),                                  (5)
```

which is nontrivial.  For any collection of Singer elements, use their
canonical permutation implementers from `(3)` on the same block.  Because
`S -> U_S` is an honest representation of `GL(V)`, every relation among
the actor matrices is also exact.  Equations `(1)--(5)` therefore give one
finite model of all their orbit norms and incidence tables with `E != 1`.

The accompanying MSI script checks the finite classification independently:
`|GL_3(F_2)|=168`, there are `48` order-seven elements, and all enumerated
tables have the asserted weights.  The proof itself is the orbit and Pauli
calculation above; enumeration is not load-bearing.

This argument does not model additional coefficient-sensitive EL20
relations outside the three-bit Pauli semidirect product, so it does not
fence a genuinely new Leavitt-prefix bridge.

No Property `(T)`, trace input, literature theorem, local computation, or
Lean compilation is used.
