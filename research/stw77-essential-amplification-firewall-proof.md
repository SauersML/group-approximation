---
rg: 2
id: stw77-essential-amplification-firewall-proof
kind: route
title: Infinite amplification makes every nonzero support essential but cannot return central isometries
target: stw77-essential-amplification-erases-finite-corners
requires:
  - stw77-bounded-operator-target-case
  - stw77-products-of-bounded-operator-targets-solve-map
  - stw77-fd-commutant-splitting-iff-proper-supports
---

Let `H=K tensor l2`. We first prove essentiality of `(EAF1)`. If
`b!=0`, faithfulness gives a unit vector `xi in K` and a number `c>0`
such that

```text
||pi(b)xi||>c.
```

For an orthonormal basis `(e_n)` of `l2`, the vectors `xi tensor e_n`
are orthonormal, while

```text
(pi(b) tensor 1)(xi tensor e_n)=pi(b)xi tensor e_n
```

are pairwise orthogonal and all have norm greater than `c`. Thus
`rho(b)` is not compact. This proves

```text
rho(B) intersect K(H)=0.                                (EAF2)
```

If `a>=0` and `rho(phi(a))!=0`, then `(EAF2)` makes this positive
operator noncompact. In `B(H)`, every noncompact positive operator is
properly infinite: for some `epsilon>0` its spectral projection on
`(epsilon,infinity)` has infinite rank, and two orthogonal isometries of
that spectral subspace give two Cuntz copies below the operator. Therefore
`rho phi` satisfies the hypothesis of
[[stw77-bounded-operator-target-case]], which proves its
`O_infinity`-stability. Notice that no property of `phi` other than being
a unital homomorphism entered this argument.

Now let

```text
D=direct_sum_j M_(n_j) subset B
```

and choose one minimal projection `p_j` in each summand. Since
`pi(p_j)!=0`, the projection

```text
rho(p_j)=pi(p_j) tensor 1
```

has infinite rank. Every infinite-rank projection in `B(H)` is properly
infinite. Applying
[[stw77-fd-commutant-splitting-iff-proper-supports]] in the ambient
bounded-operator algebra gives two orthogonal isometries in
`B(H) intersect rho(D)'`.

Apply the same equivalence in the original algebra `B`. If even one
`p_j` is not properly infinite in `B`, there cannot be two orthogonal
isometries in `B intersect D'`. Hence the amplified commutant splitting
does not descend through the faithful inclusion `rho`; infinite
amplification has changed the intrinsic Cuntz class of the bad support.

For the product statement, fix any nonempty index set `Lambda` and use the
same amplified representation in every coordinate:

```text
Phi(a)=(rho(phi(a)))_(lambda in Lambda).                (EAF3)
```

For a nonzero positive image element, choose the two Cuntz witnesses in
the single algebra `B(H)` and repeat them as constant families. They prove
proper infiniteness of `(EAF3)` in the product. The product bounded-operator
theorem gives `O_infinity`-stability there. Again the witnesses lie only in
the amplified product.

A zero-colour approximation supplies finite-dimensional algebras `D` inside
`B`. Applying `(EAF1)` to them forces all their supports to become proper
in the envelope, including precisely those supports which fail the
intrinsic criterion in `B`. Thus the product theorem cannot distinguish a
good zero-colour model from a model with a trapped finite junk corner. Any
descent must provide new norm control returning the splitting to `B`, which
is the proper-support clustering problem already isolated at the root.
