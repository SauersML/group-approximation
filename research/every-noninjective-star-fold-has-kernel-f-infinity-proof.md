---
rg: 2
id: every-noninjective-star-fold-has-kernel-f-infinity-proof
kind: route
title: Compute the two-factor quotient graph and retract every fold kernel onto it
target: every-noninjective-star-fold-has-kernel-f-infinity
requires:
  - camouflage-kernel-is-a-regular-star-amalgam
  - universal-mf-quotient
---

First observe that `B` has no proper finite-index subgroup.  If `L<B` had
finite index, the action on `B/L` would give a homomorphism

```text
B -> Sym(B/L).
```

The target is finite and hence MF, so full MF radical makes this action
trivial.  Triviality says that every element of `B` fixes the coset `L`, and
therefore belongs to `L`; hence `L=B`.  Since `D` is proper and `B` is
countable, `|B/D|=aleph_0`.

Consider the fold

```text
mu:P=B_0 *_D B_1 -> B
```

which is the identity on both factors.  Its kernel `F` intersects every
conjugate of either vertex group trivially, because `mu` is injective on
that conjugate.  Thus `F` acts freely on the Bass--Serre tree of `P`.
Because `F` is normal with quotient `B`, the quotient tree has vertex sets

```text
F\P/B_i ~= B/mu(B_i),
```

so it has one vertex of each of the two types.  Its edge set is

```text
F\P/D ~= B/D.
```

It is therefore the connected graph with two vertices and countably
infinitely many parallel edges.  Its fundamental group is `F_infinity`,
proving `(SFK2)`.

Now let `p:X->Y` be noninjective and choose distinct `x_0,x_1` in one
fiber.  The pair subamalgam

```text
P=B_(x_0) *_D B_(x_1)
```

embeds in `K_X`, and its fold kernel `F` lies in `ker(P_p)`.  Define a
retraction `r:K_X->P` by keeping these two factors and sending every other
factor identically to `B_(x_0)`.  Let

```text
gamma_X:K_X->B,   gamma_Y:K_Y->B
```

be the global folds which identify every factor.  If `mu:P->B` is the
two-factor fold, then

```text
mu after r = gamma_X = gamma_Y after P_p.
```

Hence `r(ker(P_p))<=ker(mu)=F`, while `r` is the identity on `F`.  Thus `F`
is a retract of `ker(P_p)`.

The earlier star-fold theorem shows that `ker(P_p)` is a countable free
group.  Its abelianization maps onto

```text
F_ab ~= directSum_N Z,
```

so it cannot have finite free rank.  It is therefore `F_infinity`, proving
`(SFK1)`.  The four consequences follow by applying the theorem to
equivariant maps, self-maps, and quotient maps of equivalence relations.
