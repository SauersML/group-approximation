---
rg: 2
id: finite-index-factor-induction-proof
kind: route
title: Compress the restricted induced algebra onto the base coset factor
target: finite-index-induction-transfers-non-ce-factor
requires:
  - factor-universality-character-rigidity-implies-nonhyperlinear
  - ah-groups-fail-regular-fd-character-rigidity
---

Choose left-coset representatives with the identity coset first.  In this
basis, `rho(g)` is an `n` by `n` block-monomial unitary whose nonzero entries
are values of `pi`; hence `rho(Lambda)` lies in `U(M_n(Q))`.

Let `B=rho(H)''` and let `e=e_(11)`.  The base coset `H` is fixed by left
multiplication by every element of `H`, so `e` reduces `rho|_H` and therefore

```text
e in B',
theta:B -> eM_n(Q)e,       theta(b)=ebe             (FIP1)
```

is a normal unital star homomorphism.  Its image contains
`pi(H)` and is weakly closed, so

```text
theta(B)=Q.                                           (FIP2)
```

The kernel of a normal homomorphism of finite von Neumann algebras is a
central summand.  Thus if `B` were Connes embeddable, so would its normal
quotient `Q`.  Since Connes embeddability passes from `A` to the von Neumann
subalgebra `B`, nonembeddability of `Q` forces nonembeddability of `A`.

The normalized trace of `M_n(Q)` restricts faithfully to `A`; its character
on `Lambda` therefore has GNS algebra `A`.  Disintegrate that trace over the
center of `A`.  Under regular-or-finite-dimensional factor-character
rigidity, every factorial fiber is either `L(Lambda)` or a matrix algebra.
If `L(Lambda)` were Connes embeddable, every fiber would be embeddable, and
so would their separable finite direct integral: approximate a finite moment
set first by a finite central partition and then take direct sums of
microstates for its fibers.  This contradicts nonembeddability of `A`.
Hence `L(Lambda)` is nonembeddable and `Lambda` is nonhyperlinear.

Finally, if `Lambda` is infinite simple and `H` has finite index, the core
`intersection_(g in Lambda)gHg^(-1)` is a finite-index normal subgroup.  It
cannot be trivial, since that would embed the infinite group `Lambda` in a
finite symmetric group.  Simplicity makes the core all of `Lambda`, hence
`H=Lambda`.  This proves the last assertion of the claim without any
commensurability hypothesis.
