---
rg: 2
id: qutrit-external-cyclic-router-hidden-third-proof
kind: proof
title: Compute the signed cyclic Hecke star and its D8 carrier mass
target: qutrit-external-cyclic-router-selects-only-one-hidden-third
requires:
  - qutrit-two-to-one-phase-graph-requires-central-line-twist
  - jacobson-d8-polar-has-flat-nine-phase-first-row
  - finite-overgroup-packing-preserves-hyperlinearity
---

In additive exponent notation the automorphism matrix is a signed
three-cycle. Directly,

```text
theta^3(j)=j,        theta^3(z)=z,        theta^3(w)=w,
```

so `theta` has order three and `|B|=81`. Moreover,

```text
theta^(-1)(j)=z^(-1),        theta^(-1)(z)=w.
```

For `U=g^(-1)` this gives

```text
U C U^(-1)=<z,w>,
C intersect U C U^(-1)=<z>,                            (QER3)
U^(-1) z U=gzg^(-1)=j^(-1).
```

Apply the character double-coset criterion to `p_b U p_a`. On the
generator `z` of the intersection, its two sides are

```text
chi_b(z)=omega^b,
chi_a(U^(-1)zU)=chi_a(j^(-1))=omega^2.
```

They agree exactly when `b=2`. In that case the standard finite-group
calculation gives

```text
||p_b U p_a||_2^2
 =|C intersect U C U^(-1)|/|C|^2
 =3/81=1/27.                                           (QER4)
```

This proves the star graph `(QER1)`.

The norm already signals that a full source is not transported:
`tau(p_a)=1/9`, so `(QER4)` is only one third of the source trace.
The missing cut can be identified exactly. Put `Y_a=p_2 U p_a`.
Since `E` is abelian, the character projections which occur in the two
Gram operators commute. For the initial Gram operator,

```text
Y_a^*Y_a=p_a g p_2 g^(-1)p_a.                          (QER5)
```

The projection `g p_2 g^(-1)` is the transported character projection
on `theta(C)=<w,j>`. Its character has value `omega^2` on `w` and
`omega` on `j`. Multiplication by `p_a` therefore gives the single
`E`-character atom

```text
lambda_a(j)=omega,       lambda_a(z)=omega^a,
lambda_a(w)=omega^2.                                    (QER6)
```

Similarly,

```text
Y_aY_a^*=p_2 g^(-1)p_a g p_2                           (QER7)
```

is the `E`-character atom

```text
mu_a(j)=omega,           mu_a(z)=omega^2,
mu_a(w)=omega^a.                                        (QER8)
```

Thus both Gram operators are projections. This proves that `Y_a` is a
partial isometry, and each Gram projection has trace `1/|E|=1/27`.
For distinct `a` the atoms in both `(QER6)` and `(QER8)` are
orthogonal. The two selected sources therefore land in two distinct hidden
`w`-phases below `p_2`; the third target phase remains unused.

Now identify `w` with a second-qutrit Pauli generator which commutes with
`j=J` and `z=Z_1`. Then `E` is a subgroup of the order-`3^5`
qutrit packet `F_q`. Let

```text
f_eta=V_eta V_eta^*.
```

The D8 polar calculation gives `tau(f_eta)=1/32` and proves trace
factorization between `C[F_q]` and the active two-group supporting
`f_eta`. Since `Y_a^*Y_a=z_(E,lambda_a)`,

```text
||Y_a V_eta||_2^2
 =tau(V_eta^* z_(E,lambda_a)V_eta)
 =tau(z_(E,lambda_a)f_eta)
 =(1/27)(1/32)
 =1/864.                                                (QER9)
```

The initial atoms for `a=0,1` are orthogonal, so the cross terms vanish
and

```text
||(Y_0+Y_1)V_eta||_2^2=2/864=1/432.                    (QER10)
```

On the other hand, flatness of the three `C` phases gives

```text
||(p_0+p_1)V_eta||_2^2=2/288=1/144,
||p_2V_eta||_2^2=1/288.                                (QER11)
```

Equations `(QER9)--(QER11)` show simultaneously that the router retains
one third of the selected source and occupies two thirds of the
complementary target. There is no hidden normalization that turns its
Hecke star into a full carrier.

Finally, `B` is finite and `E` is finite. Attaching `B` to the base
along `E` is exactly a finite-overgroup amalgam, so the finite-overgroup
packing theorem extends every hyperlinear model of the base across this
attachment. Attaching finitely many independent copies does not change that
conclusion. Hence a bare collection of these routers cannot make the
Jacobson or Leavitt base nonhyperlinear; a further joint relation on their
multiplicity spaces would have to do the load-bearing work.
