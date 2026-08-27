---
rg: 2
id: leavitt-unit-internal-mf-reflection-tower-proof
kind: route
title: Iterate the bilateral Leavitt shift and pull the MF reflection through each wreath layer
target: leavitt-unit-internal-mf-reflection-tower
requires:
  - leavitt-unit-internal-wreath-universality
  - leavitt-unit-internal-shift-reflection
---

The finite-level theorem supplies `K_0=U wr F<=U`, the quotient
`pi_0:K_0->F`, and a nonidentity involution `d` normally generating
`ker(pi_0)`.

## One induction step

Suppose `K<=U` is finitely generated and has an epimorphism `pi:K->Q` with

```text
Rad_MF(K)=ker(pi)=normalClosure_K(d),                    (IRP1)
```

where every quotient of `Q` is MF.  Use the bilateral antichain and shift
unit of `leavitt-unit-internal-shift-reflection`, but put the subgroup `K<=U`
in each corner instead of all of `U`.  The same formulas embed

```text
K wr Z=K^(Z) semidirectProduct Z <= U.                  (IRP2)
```

Applying `pi` coordinatewise gives an epimorphism

```text
Pi:K wr Z -> Q wr Z                                    (IRP3)
```

with kernel `ker(pi)^(Z)`.

Every MF-target map from `K wr Z` restricts on each coordinate copy of `K`
to a map that kills `ker(pi)`.  It therefore kills `ker(pi)^(Z)` and factors
uniquely through `(IRP3)`.  If `Q wr Z` is MF, its identity map detects every
element outside that kernel, so

```text
Rad_MF(K wr Z)=ker(pi)^(Z).                             (IRP4)
```

Conjugation by the shift moves coordinate zero through all coordinates.
Together with `(IRP1)`, this shows that the copy of `d` in coordinate zero
normally generates the kernel in `(IRP4)`.

If every quotient of `Q wr Z` is MF, then for any normal `N` the maps to MF
groups which kill `N` factor through the exact quotient

```text
(Q wr Z)/Pi(N).
```

Pulling its trivial MF radical back gives

```text
cl_MF^(K wr Z)(N)=N ker(Pi),                            (IRP5)
```

which is the one-word closure formula.

## Iteration

Each `Q_m` is amenable: finite groups are amenable, restricted direct sums
of amenable groups are amenable, and extensions of amenable groups are
amenable.  Every quotient of `Q_m` is therefore amenable and MF.  The same
holds for `Q_m wr Z`, so the induction step applies at every level.  A finite
generating set for `K_m` in coordinate zero together with the shift generates
`K_(m+1)`.  This proves all reflection, radical, closure, embedding, and
finite-generation assertions.

Finally, let `A` be nontrivial solvable of derived length `l`, and put
`G=A wr Z` with shift `t`.  Since `G/A^(Z)` is abelian, `G'<=A^(Z)`, so
`derivedLength(G)<=l+1`.  On the other hand, for `a in A`, the commutator of
the element supported by `a` at coordinate zero with `t` has entries
`a^(-1)` and `a` in two adjacent coordinates.  Coordinate-zero projection
therefore maps `G'` onto `A`.  It maps the `(l-1)`st derived subgroup of
`G'` onto the `(l-1)`st derived subgroup of `A`, which is nontrivial.  Hence
`G^(l)!=1`, and

```text
derivedLength(A wr Z)=derivedLength(A)+1.
```

Starting from `C_2` proves `derivedLength(Q_m)=m+1`.  Since the universal MF quotient is invariant under
isomorphism, the corresponding `K_m` are pairwise nonisomorphic.
