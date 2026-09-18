---
rg: 2
id: fg-metabelian-groups-have-roots-at-finitely-many-primes-proof
kind: route
title: The derived subgroup is a finitely generated module over a finitely generated commutative ring, so generic freeness bounds the primes dividing an element
target: fg-metabelian-groups-have-roots-at-finitely-many-primes
requires: []
---

Direct proof. Write `M = G'` additively and `Q = G/G'`.

**Step 1: `M` is a finitely generated `Z[Q]`-module.**
- `Q` is a finitely generated abelian group, hence finitely presented. Choose a
  finite generating set of `G`. Then `M` is the normal closure in `G` of the
  finitely many words that map to the relators of a finite presentation of `Q`.
- Conjugation by `G` acts on the abelian group `M` through `Q`. So the normal
  closure of those words is the `Z[Q]`-submodule they generate.
- `Z[Q]` is a finitely generated commutative ring.

**Step 2: generic freeness.** Eisenbud, *Commutative Algebra with a View Toward
Algebraic Geometry*, Theorem 14.4 (generic freeness): if `A` is a noetherian
domain, `B` a finitely generated `A`-algebra and `N` a finitely generated
`B`-module, there is `0 ≠ a ∈ A` such that `N[a^{-1}]` is a free
`A[a^{-1}]`-module. Take `A = Z`, `B = Z[Q]` and `N = M`, and get an integer
`a ≠ 0` such that `F = M[1/a]` is a free `Z[1/a]`-module.

**Step 3: item 1.**
- Let `x ∈ M` have infinite order. The kernel of `M -> F` is the `a`-power
  torsion, so the image `x̄` of `x` is nonzero. Write `x̄` in a basis of `F` and
  pick a coordinate `x_i ≠ 0` in `Z[1/a]`.
- Let `q ∤ a` be a prime with `y^q = x` for some `y ∈ G`. The image of `y` in `Q`
  has order dividing `q`. `Q` is a finitely generated abelian group, so its
  torsion has finite exponent `e`. If also `q ∤ e`, then `y ∈ G' = M`, and
  `x = q·y` in `M`.
- Then `x_i = q·y_i` with `y_i ∈ Z[1/a]`. So `q` divides the numerator of `x_i`,
  a fixed nonzero integer.
- Only finitely many primes `q` do this, or divide `a·e`.

**Step 4: item 2.**
- Let `P` be infinite and suppose `ι: Z[1/P] -> G` is injective. The image `B` of
  `ι(Z[1/P])` in `Q` is a subgroup of a finitely generated abelian group, so it
  is finitely generated.
- `B` is `q`-divisible for every `q ∈ P`. A finitely generated abelian group
  `Z^r ⊕ T` that is `q`-divisible for infinitely many `q` has `r = 0`, so `B`
  is finite, of order `b` say.
- Then `x = ι(b) ∈ G'` has infinite order. For every `q ∈ P` it has the `q`-th
  root `ι(b/q)`. This contradicts item 1.
