---
rg: 2
id: fiber-product-conjugation-action-lemma
kind: claim
title: The fiber product of a group with itself over a quotient acts transitively on the kernel with diagonal stabilizer, conjugacy-class pair orbits and diagonal-centralizer kernel
distinct_from:
  mihailova-nonseparable-coset-stabilizer: that uses a Mihailova fiber product of a free group over a quotient to build a nonseparable coset stabilizer, an obstruction to finite approximation; this computes the orbit and stabilizer data of the two-sided translation action of a fiber product on the kernel, and is used to VERIFY a finiteness criterion rather than to defeat one.
  simple-core-bi-index-counts-coset-action-pair-orbits: that identifies the pair orbits of a COSET action with a double coset set; this identifies the pair orbits of a two-sided translation action on a normal subgroup with conjugacy classes, and its point stabilizer is a diagonal rather than the acting point stabilizer of a coset action.
  twisted-brin-thompson-finite-presentation-criterion: that is an imported equivalence about twisted Brin-Thompson groups; this is an elementary group-theoretic computation about one action and mentions no Brin-Thompson group.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let

    1 -> N -> T -pi-> Q -> 1

be exact and let

    Gamma  =  T x_Q T  =  { (a,b) in T x T : pi(a) = pi(b) }

be the fiber product.  Then

    (a,b) . x  =  a x b^{-1}

is a well-defined action of `Gamma` on the set `N`, and

1. it is **transitive**;
2. `Stab_Gamma(1) = Delta T`, the diagonal, and every point stabilizer is
   conjugate to it;
3. the `Gamma`-orbits on ordered pairs of elements of `N` are in natural
   bijection with the `T`-conjugacy classes of `N`;
4. the kernel of the action is `Delta C_T(N)`, so the action is faithful
   exactly when `C_T(N) = 1`.

## Proof

*Well-defined.*  `pi(a x b^{-1}) = pi(a) pi(b)^{-1} = 1` because `x in N` and
`pi(a) = pi(b)`, so `a x b^{-1} in N`.  It is an action:
`(a,b)(c,d) . x = (ac) x (bd)^{-1} = a (c x d^{-1}) b^{-1}`.

*Transitive.*  For `x in N` the pair `(x,1)` lies in `Gamma`, since
`pi(x) = 1 = pi(1)`, and `(x,1) . 1 = x`.

*Point stabilizer.*  `(a,b) . 1 = a b^{-1}`, which is `1` exactly when
`a = b`.  So `Stab_Gamma(1) = Delta T`.  Transitivity makes the remaining
point stabilizers conjugate to this one.

*Pair orbits.*  Given `(x,y) in N x N`, the element `(x^{-1},1) in Gamma`
carries it to `(1, x^{-1} y)`.  Two pairs with first coordinate `1` lie in
one orbit exactly when their second coordinates lie in one orbit of
`Stab_Gamma(1) = Delta T`, and `(t,t) . z = t z t^{-1}`.  So the map
`(x,y) |-> [x^{-1} y]` is a bijection from ordered-pair orbits to
`T`-conjugacy classes of `N`.

*Kernel.*  An element acting trivially fixes `1`, hence is `(t,t)`; and
`(t,t)` fixes every `x in N` exactly when `t` centralizes `N`.  So the kernel
is `Delta C_T(N)`.  `∎`

## Two consequences used downstream

**Unordered pairs.**  Orbits of two-element subsets of `N` are quotients of
orbits of ordered pairs of distinct elements, so clause 3 makes finiteness of
the `T`-conjugacy class set of `N` sufficient for the fourth clause of
`type-a-action-gives-boone-higman-for-subgroups`.  The converse is not
claimed and is not needed.

**The diagonal copy.**  `Delta T <= Gamma` always, so anything embedded in
`T` is embedded in `Gamma`.  This is what makes the lemma usable as a
transfer: the group one cares about never has to act on anything.

## Screening tests the lemma hands over for free

Any `T, N` meeting clauses 3 and 4 with finitely many classes and trivial
centralizer satisfies:

* `Z(N) = 1`, since `Z(N) <= C_T(N)`.
* `N` realizes only finitely many element orders, since conjugate elements
  have equal order and the order function factors through the finite class
  set.  If `N` is torsion this forces finite exponent; it does **not** force
  finite exponent in general, and a group with finitely many conjugacy
  classes and elements of infinite order exists, so this is a screen and not
  an obstruction.
* If `N` is finite then `T` embeds in `Aut(N)` by clause 4, so `T` is finite.
  Any application to an infinite group therefore needs an infinite `N`.
