# The factorized BS(1,4) gate has only one dihedral reflection

Date: 2026-08-14

## 1. Outcome

In a fixed central sector `epsilon in {+1,-1}`, the factorization

```text
C=AB,       A^2=B^2=epsilon 1                         (DRB1)
```

is exactly equivalent to one projective-dihedral relation:

```text
A^2=epsilon 1,
A^(-1) C A=C^(-1),
B=A^(-1)C.                                             (DRB2)
```

Consequently the factorized `BS(1,4)` repair problem does not have two
independent factor variables.  Eliminate `B`.  The exact Iwahori sector is
the three-unitary relation set

```text
A^2=epsilon 1,
A^(-1) C A=C^(-1),
(A X^2)^3=epsilon 1,
(A^(-1) C X)^3=epsilon 1,
C X C^(-1)=X^4.                                      (DRB3)
```

Thus the live nonlinear theorem is **reflection-preserving `BS(1,4)`
repair**: repair the fourth-power dynamics while retaining one projective
reflection and the two order-three modular relators.  There is no separate
factorization or second-reflection gauge after `(DRB2)`.

This is a quantitative Tietze reduction.  A correction of `(A,C,X)` gives a
correction of `B` with no dimension loss and with movement bounded by the
sum of the movements of `A` and `C`.

## 2. Elimination of the second Weyl unitary

Assume `(DRB1)`.  Since `epsilon^2=1`,

```text
A^(-1)=epsilon A,
B^(-1)=epsilon B,
C^(-1)=B^(-1)A^(-1)=BA.                              (DRB4)
```

Moreover,

```text
A^(-1) C A
 =epsilon A(AB)A
 =epsilon A^2 BA
 =BA
 =C^(-1).                                             (DRB5)
```

Finally `C=AB` gives

```text
B=A^(-1)C.                                             (DRB6)
```

This proves `(DRB2)` from `(DRB1)`.

Conversely, assume `(DRB2)` and define `B=A^(-1)C`.  Then `AB=C`.  The
reflection relation gives

```text
C A^(-1)=A^(-1) C^(-1).                              (DRB7)
```

Therefore

```text
B^2
 =A^(-1) C A^(-1) C
 =A^(-2) C^(-1)C
 =A^(-2)
 =epsilon 1.                                          (DRB8)
```

So `(DRB1)` and `(DRB2)` are equivalent.

Before fixing the central sector, introduce a central involution `z`.  The
same calculation gives the exact Tietze equivalence

```text
C=AB, A^2=B^2=z

<=>

A^2=z, A^(-1)CA=C^(-1), B=A^(-1)C.                   (DRB9)
```

No division by a scalar and no representation-specific choice enters this
identity.

## 3. Elimination in the modular presentation

The modular group presentation used in the Iwahori reduction is

```text
SL_2(Z)=<w,u | w^4=1, (wu)^3=w^2>.                   (DRB10)
```

On the fixed sector, the first vertex sends

```text
w |-> A,       u |-> X^2,                             (DRB11)
```

and the second sends

```text
w |-> B,       u |-> X.                               (DRB12)
```

Their exact modular relations are therefore

```text
A^2=B^2=epsilon 1,
(A X^2)^3=(B X)^3=epsilon 1.                          (DRB13)
```

The factorized dynamical relation is

```text
(AB)X(AB)^(-1)=X^4.                                   (DRB14)
```

Put `C=AB` and use `(DRB2)`.  Substitution of
`B=A^(-1)C` in `(DRB13)--(DRB14)` gives exactly `(DRB3)`.
Conversely, a solution of `(DRB3)` defines `B=A^(-1)C`; equations
`(DRB8)` and `(DRB13)--(DRB14)` recover the factorized presentation.

The central-variable version is

```text
<z,A,C,X |
 z^2=1, z central,
 A^2=z,
 A^(-1) C A=C^(-1),
 (A X^2)^3=z,
 (A^(-1) C X)^3=z,
 C X C^(-1)=X^4>.                                    (DRB15)
```

It is Tietze equivalent to `(FBS22j)` in
`TRUE_IWAHORI_MATCHING_REDUCES_TO_FACTORIZED_BS14_REPAIR.md` by adjoining
or eliminating `B=A^(-1)C`.

## 4. Quantitative equivalence of correction problems

Let `(A,B,X)` be an initial pair with exact common central square and put
`C=AB`.  Then the first two relations in `(DRB3)` hold exactly before any
Iwahori repair.

Suppose `(A',C',X')` is an exact solution of `(DRB3)` and define

```text
B'=(A')^(-1)C'.                                       (DRB16)
```

The preceding sections show that `(A',B',X')` is an exact solution of the
factorized Iwahori presentation.  For normalized Hilbert--Schmidt norm,

```text
||B'-B||_2
 <=||(A')^(-1)C'-(A')^(-1)C||_2
   +||(A')^(-1)C-A^(-1)C||_2
 =||C'-C||_2+||A'-A||_2.                              (DRB17)
```

Thus small movement of `(A,C,X)` gives small movement of `(A,B,X)` with an
absolute constant.

In the other direction, from a corrected factorized triple
`(A',B',X')`, set `C'=A'B'`.  Then

```text
||C'-C||_2<=||A'-A||_2+||B'-B||_2.                    (DRB18)
```

Equations `(DRB17)--(DRB18)` prove quantitative equivalence, including in
the flexible metric after negligible padding.

## 5. The narrower stability interface

The first two relations in `(DRB3)` define a projective central extension
of the infinite dihedral group.  After removing the fixed scalar phase, the
pair `(A,C)` is an involutive reflection of the cyclic stable-letter
direction.  Virtually cyclic groups are Hilbert--Schmidt stable, so the
reflection relation itself is not the source of the open problem.

The third and fourth relations say that the two words

```text
A X^2,          A^(-1) C X                            (DRB19)
```

have the prescribed projective order three.  The last relation is the
`BS(1,4)` dynamics.  The modular group is Hilbert--Schmidt stable in its own
generator variables, as are the virtually cyclic reflection group and
`BS(1,4)`.  Applying those theorems separately need not preserve the shared
square root `X`, the reflected stable letter `C`, or the two order-three
words.  The unresolved assertion is exactly this shared-variable
synchronization.

The corrected endpoint can be stated as follows.

> **Reflection-preserving `BS(1,4)` repair.**  Every normalized-HS almost
> solution of `(DRB3)` for which the projective-dihedral and the two modular
> vertex relations are exact is flexibly close to an exact solution of all
> five relations.

By the quantitative Tietze equivalence above, this theorem is equivalent to
factorized `BS(1,4)` repair and hence to the Dogon--Vigdorovich Iwahori
matching question.  Its advantage is structural: it has one Weyl/reflection
variable rather than two factors whose corrected product must be split.

## 6. Status

The eliminations `(DRB1)--(DRB18)` are exact.  Reflection-preserving repair
is not proved here.  The reduction removes an artificial second-factor
degree of freedom but does not supply the regular-sector basin capture or
the harmonic-integrability estimate required for a complete
nonhyperlinearity proof.

## References

- M. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*,
  [arXiv:2506.20843v2](https://arxiv.org/abs/2506.20843v2), Question 1.4.
- A. Levit and I. Vigdorovich, *Characters of solvable groups,
  Hilbert--Schmidt stability and dense periodic measures*,
  [arXiv:2206.02268](https://arxiv.org/abs/2206.02268), for the
  `BS(1,n)` stability input.
