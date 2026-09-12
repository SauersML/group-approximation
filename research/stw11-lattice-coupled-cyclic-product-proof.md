---
rg: 2
id: stw11-lattice-coupled-cyclic-product-proof
kind: route
title: Detect every active cyclic factor and embed the lattice crossed product into their tensor product
target: stw11-lattice-coupled-cyclic-products-are-af-embeddable
requires:
  - pimsner-cyclic-transformation-af-equivalence
artifacts:
  - research/artifacts/stw11-lattice-coupled-cyclic-products-audit-2026-08-30.md
---

Put `A=C(product_i X_i)`, `H=L(Z^d)`, and `K=ker(L)`.  All crossed
products below may be read as full or reduced because the acting groups are
abelian.

## 1. Remove the trivially acting kernel

The subgroup `H` of `Z^m` is free abelian.  Hence

```text
0 -> K -> Z^d -> H -> 0
```

splits, and `Z^d=K direct_sum H` after choosing a section.  The action of `K`
is trivial, so the universal covariant relations give

```text
A rtimes Z^d ~= (A rtimes H) tensor C*(K).                 (LC2)
```

In particular, `A rtimes H` embeds unitally in `A rtimes Z^d`.  Stable
finiteness passes to C*-subalgebras, so condition 1 implies that `A rtimes H`
is stably finite.

## 2. Stable finiteness detects each active cyclic system

Fix an active coordinate `i`.  Choose `h in H` with nonzero `i`-th
coordinate `q`.  Inside `A rtimes H`, use the coordinate copy of `C(X_i)`
and the canonical unitary `u_h`.  They give a covariant homomorphism

```text
theta_i:C(X_i) rtimes_(alpha_i^q) Z -> A rtimes H,
theta_i(f)=1 tensor ... tensor f tensor ... tensor 1,
theta_i(v)=u_h.                                             (LC3)
```

This map is injective.  Indeed, the faithful coefficient expectations on the
two reduced crossed products satisfy

```text
E_H theta_i = theta_i E_i.
```

The identity is immediate on finite Fourier sums, since `nh` is nonzero for
every nonzero integer `n`; faithfulness of `E_i` then proves injectivity.
Consequently

```text
C(X_i) rtimes_(alpha_i^q) Z
```

is stably finite.

Pimsner's theorem identifies stable finiteness of a cyclic transformation
crossed product with the absence of an open compression.  We only need the
following elementary power check to return from `alpha_i^q` to `alpha_i`.
If

```text
alpha_i(U) proper_subset U,
```

then `alpha_i(U) subset U`, and for every positive `n`,

```text
alpha_i^n(U) subset alpha_i(U) proper_subset U.             (LC4)
```

For negative powers, the crossed products by `alpha_i^n` and
`alpha_i^(-n)` are isomorphic by reversing the implementing unitary.  Thus a
compression for `alpha_i` would contradict stable finiteness of the algebra
in `(LC3)`.  Pimsner's theorem now says that

```text
B_i=C(X_i) rtimes_(alpha_i) Z
```

is stably finite and, more strongly, AF-embeddable.  This proves `1=>2=>3`;
Pimsner also gives `3=>2`.

## 3. Assemble one AF host

Let `I` be the set of active coordinates.  The action of `H` is trivial on
the other factors.  The inclusion of the subgroup `H subset Z^I` gives a
faithful inclusion of reduced crossed products, again by coefficient
expectations:

```text
A rtimes H
 -> (tensor_(i in I) B_i) tensor C(product_(i notin I) X_i). (LC5)
```

For completeness, the crossed product by the coordinatewise `Z^I`-action is
the tensor product of the cyclic crossed products `B_i`; `(LC5)` is its
canonical subgroup inclusion, tensored with the inactive coefficient algebra.

Each active `B_i` embeds in an AF algebra by Step 2.  Every commutative
separable unital C*-algebra is AF-embeddable: a compact metrisable spectrum is
a continuous image of the Cantor set, so pullback embeds its function algebra
in the AF algebra of continuous functions on the Cantor set.  This applies
both to the inactive coefficient algebra in `(LC5)` and to

```text
C*(K) ~= C(T^(rank K)).
```

Finite spatial tensor products of faithful embeddings remain faithful, and a
finite tensor product of AF algebras is AF.  Combining `(LC2)` and `(LC5)`
therefore embeds `A rtimes Z^d` in an AF algebra.  This proves `1=>4`.

AF-embeddability implies quasidiagonality, and quasidiagonality implies stable
finiteness, giving `4=>5=>1`.  Conversely, condition 2 feeds the same assembly
without Step 2, proving `2=>4`.  Together with Pimsner's cyclic equivalence,
all five conditions follow.
