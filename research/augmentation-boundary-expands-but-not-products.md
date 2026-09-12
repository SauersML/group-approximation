---
rg: 2
id: augmentation-boundary-expands-but-not-products
kind: claim
title: The Kazhdan Cayley boundary exposes the whole augmentation module but not its product table
distinct_from:
  finite-orbital-checksum-cannot-expose-sl3-coset-module: that treats finitely many double-coset orbitals for one arithmetic coset action; this gives the universal regular-augmentation boundary map, its positive Kazhdan estimate, and the complementary graph-product obstruction.
  relative-kazhdan-bimodule-upgrades-finite-covariance: that upgrades covariance after an exact module representation has been supplied; this shows that a bounded-degree linear presentation of the module does not supply that representation.
  finite-presentation-must-expose-whole-module-with-uniform-defect: that asks for uniform multiplicativity in matrix models; this separates the part achieved by one bounded-degree map from the nonlinear part that remains open.
---

Let `A` be an infinite finitely generated property-`(T)` group with finite
symmetric Kazhdan generating set `S`, and let

```text
I_A={f in F_2^(A) with finite support and sum_g f(g)=0}
```

be the regular binary augmentation module.  The degree-`2` Cayley boundary

```text
partial:F_2^(A times S)->I_A,
partial(g,s)=e_g+e_(gs),                                (ABE1)
```

is `A`-equivariant and onto.  Its analytic transpose, the Cayley gradient

```text
(d xi)(g,s)=xi(gs)-xi(g),                               (ABE2)
```

has the dimension-independent Kazhdan lower bound

```text
sum_(s in S)||lambda(s)xi-xi||_2^2
 >= kappa^2 ||xi||_2^2.                                (ABE3)
```

Thus one fixed bounded-degree map really does expose every LINEAR
augmentation coefficient.

It does not expose the multiplicative table of the elementary abelian lamp
group.  Given any finite family of bounded-support words in the point
involutions `{c_g:g in A}` which are valid when all lamps commute, together
with all their `A`-translates, there is an exact semidirect-product model

```text
K_D rtimes A                                             (ABE4)
```

where `K_D` is an `A`-invariant graph product of vertex `C_2` groups, every
listed word is trivial, every boundary lamp `c_g c_(gs)` is present, but
some remote pair of point lamps does not commute.  Hence the induced
boundary words do not form a representation of the abelian module `I_A`.

Consequently a Cayley/LDPC boundary gadget can solve coefficient exposure
and still fail `(FME1)` maximally at zero local defect.  The exact missing
operation is uniform **abelianization** of the graph-product lamp kernel.
Only after that operation produces a genuine representation of `I_A` can
`relative-kazhdan-bimodule-upgrades-finite-covariance` apply.  Relative
property `(T)` supplies the subsequent whole-module covariance estimate; it
does not turn the bounded-degree linear chain map into a multiplicative
module decoder.

For residually finite `A`, even the proposed analytic abelianization of this
concrete kernel is impossible from the graph relations alone.
`finite-graph-product-amplifications-block-hs-collapse`
separates every missing commutator in a finite actor quotient and then in an
arbitrarily amplified finite-dimensional exact representation, where its
normalized-HS distance from the identity is `sqrt(2)`.  This also applies
when `A` has property `(T)` and the finite quotient Cayley graphs are
expanders.  Thus the residual is narrower than generic ``HS abelianization'':
one must add a genuinely new controller relation which is not already valid
in the partial graph product and whose finite-dimensional consequences kill
all missing edges.
