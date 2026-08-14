# The atlas kernel does not have bounded normal width

Date: 2026-08-14

## Outcome

A tempting way to cross the finite-coordinate multiplication gate is false.
Let

```text
P=A8*A8,
N=ker(P -> U_Q)=[P,R]
```

be the exact atlas source and its central-extension kernel.  A finite set
`S subset N` normally generates `N`, but there is no constant `C` such that
every member of `N` is a product of at most `C` conjugates of elements of
`S union S^(-1)`.

Thus small normalized-Hilbert--Schmidt defect on the printed normal
generators cannot be propagated to every dimension-dependent coefficient
relation with a uniform telescoping constant.  The normal width two statement
for the survivor in the quotient `Q` does not change this: it controls
generation of `Q`, not relation area inside the kernel `N`.

## Quasimorphism obstruction

The free product `P=A8*A8` acts non-elementarily and properly on its
Bass--Serre tree.  Both vertex factors embed in `U_Q`, so `N` intersects
every conjugate of a vertex factor trivially.  The nontrivial normal subgroup
`N` is therefore infinite and acts non-elementarily on the tree.

The Bestvina--Fujiwara counting construction supplies a homogeneous
quasimorphism

```text
q:P -> R
```

which is nonzero on some `g in N`.  Equivalently, one may choose a chiral
loxodromic element of the non-elementary `N`-action and homogenize its
counting quasimorphism.  Write `D>=0` for the defect of `q` and put

```text
M=max_(s in S) |q(s)|.
```

Homogeneous quasimorphisms are conjugation invariant and send inverses to
negatives.  If

```text
x=c1 s1^(+-1) c1^(-1) ... cm sm^(+-1) cm^(-1),
```

with every `si in S`, repeated use of the defect inequality gives

```text
|q(x)| <= m M + (m-1)D <= m(M+D).                    (KNW1)
```

Apply `(KNW1)` to `x=g^k`.  Homogeneity gives

```text
k |q(g)|=|q(g^k)| <= m(M+D),                         (KNW2)
```

so the required number `m` grows at least linearly with `k`.  No bounded
normal width exists.

The quantitative list-product estimate and its signed-conjugate corollary
are formalized source-first in
`GroupApproximation/Monsters/TwoConjugacyClasses.lean` as

```text
abs_list_prod_le_of_quasimorphism
abs_list_prod_le_of_signedConjugates
signedConjugate_length_unbounded_on_powers
```

No local or remote build was run for this edit.

## Consequence for the hyperlinearity program

Suppose an exact representation of `P` sends each member of `S` within
normalized-HS distance `delta` of the identity.  A displayed decomposition
of `n in N` into `m(n)` conjugated relators only gives the elementary bound

```text
||pi(n)-1||_2 <= m(n) delta.                          (KNW3)
```

The theorem above proves that `m(n)` cannot be bounded independently of
`n`.  In the radical-pairing extraction, the needed coefficient relations
depend on the finite matrix coordinate and can move out to elements whose
normal area grows faster than `1/delta`.  Finite normal generation therefore
does not turn the asymptotic atlas model into a globally accurate
representation of all root coefficients.

This closes only the algebraic bounded-width shortcut.  A dimension-free
analytic theorem could still use spectral gap, conditional expectations, or
the carrier-specific cross-root structure without estimating each kernel
word separately.  The live endpoint remains:

> prove directly that the transported Pauli carrier is asymptotically
> measurable in the parent binary algebra, or equivalently recover the
> paired radical quotient with total error controlled by the fixed relator
> packet rather than by the normal area of dimension-dependent words.

## Primary source

- M. Bestvina and K. Fujiwara, *Bounded cohomology of subgroups of mapping
  class groups*, [arXiv:math/0012115](https://arxiv.org/abs/math/0012115),
  for the counting-quasimorphism mechanism on non-elementary WPD actions.
