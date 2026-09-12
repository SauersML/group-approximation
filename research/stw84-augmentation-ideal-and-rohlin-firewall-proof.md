---
rg: 2
id: stw84-augmentation-ideal-and-rohlin-firewall-proof
kind: route
title: Apply Brown, split off augmentation, and rule out ordinary Rokhlin towers
target: stw84-cyclic-local-finite-af-embeddable
requires:
  - brown-af-automorphism-crossed-product-equivalence
artifacts:
  - research/artifacts/stw84-cyclic-group-af-action-2026-08-30.md
---

## 1. AF-embeddability is automatic

Because `K` is countable locally finite, `B=C*(K)` is a separable unital AF
algebra.  The semidirect product `G` is amenable.  Hence its full and reduced
group C-star algebras agree, and the regular trace on `C*(G)` is faithful.
A unital C-star algebra with a faithful trace is stably finite: the amplified
trace is faithful on every matrix algebra and rules out a proper isometry.
Therefore `B rtimes_alpha Z` is stably finite.  Brown's AF-coefficient
crossed-product equivalence now makes it AF-embeddable and quasidiagonal.

## 2. Remove the fixed scalar fiber exactly

The augmentation ideal `I_K` is `alpha`-invariant, because

```text
epsilon(alpha(lambda_k))=epsilon(lambda_(alpha(k)))=1.
```

The quotient action on `B/I_K=C` is trivial.  Since `Z` is exact, reduced
crossed products preserve the short exact sequence; amenability again
identifies full and reduced crossed products.  Thus

```text
0 -> I_K rtimes_alpha Z
  -> B rtimes_alpha Z
  -> C rtimes_id Z
  -> 0.
```

The last algebra is `C(T)`, proving `(CAF1)`.  The nuclear-dimension extension
inequality

```text
dim_nuc(E)<=dim_nuc(J)+dim_nuc(E/J)+1
```

and `dim_nuc(C(T))=1` give `(CAF2)`.

## 3. Ordinary Rokhlin dimension cannot see this problem

Rokhlin dimension for integer actions passes to equivariant quotients.  It
therefore suffices to check that the trivial action on `C` has infinite
Rokhlin dimension.  This can also be seen directly from the central-sequence
order-zero formulation.  For a tower height `n>=2`, an equivariant cpc
order-zero map

```text
C(Z/nZ) -> C_infinity
```

must send all minimal projections to the same positive element, because the
target action is trivial and the source shift is transitive.  Order zero
makes those equal images orthogonal, so they are zero.  Hence no finite
collection of equivariant order-zero tower maps can sum to the unit.  The
trivial action has infinite Rokhlin dimension, and so does the original
unital action on `B`.

This argument concerns ordinary Rokhlin dimension.  It does not rule out a
relative tower theorem on `I_K`, which is exactly why `(CAF1)` is the useful
replacement.

## 4. The alternating shift is approximately inner

Let `K=Alt_fin(Z)` and let `alpha` be translation of the underlying set by
one.  Given a finite subset `F subset K`, let `S subset Z` contain the
supports of all its elements.  The finite partial bijection

```text
s |-> s+1,       s in S,
```

extends to a finitary permutation `p` of `Z`.  If necessary, multiply by a
transposition on two fresh points outside the support of `p` to make `p`
even.  Then
`p in K` and

```text
alpha(g)=p g p^(-1),       g in F.                     (CAF3)
```

Exhausting `K` by finite sets produces group unitaries `lambda_p` for which
`Ad(lambda_p)` converges point-norm to the induced automorphism of `C*(K)`.
Thus it is approximately inner.

On the other hand, if `a=(0,1,2)`, then the orbit

```text
alpha^n(a)=(n,n+1,n+2),       n in Z,
```

generates `Alt_fin(Z)`.  Its orbit-generated subgroup is infinite, so the
equivalent invariant-finite-exhaustion/kernel-finiteness conditions from
`stw84-locally-finite-by-abelian-reduces-to-twisted-af-lattices` fail.
