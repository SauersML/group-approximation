---
rg: 2
id: mf-residual-amenable-quotient-criticality-proof
kind: route
title: Restrict the residual along the amenable quotient, then read off the finite, amenable and Kazhdan consequences
target: mf-nonhyperlinear-residual-with-amenable-quotient-is-critical
requires:
  - hyperlinear-residual-restricts-along-amenable-quotients
  - mf-nonhyperlinear-collapse-structure
  - kazhdan-mf-hyperlinear-fragment
  - mf-characterless-corona-image-has-hyperlinear-quotient
  - hyperlinear-visibility-transfers-across-finite-index
---

## Why sufficient

Write `Res(K)` for the hyperlinear residual of a countable group `K`, and
`R = Res(G)`. By `mf-nonhyperlinear-collapse-structure`, a countable group
`K` is hyperlinear exactly when `Res(K) = 1`, and `Res(K)` is the set of
elements of `K` that are not tracially visible.

**Part 1.** Suppose `G/R` is amenable. By part 1 of
`hyperlinear-residual-restricts-along-amenable-quotients` applied to `N = R`,

```text
Res(R) = Res(G) intersect R = R.
```

- *`R` is MF.* Restricting an injective homomorphism from `G` into the unitary
  group of the norm matrix corona to `R` keeps it injective.
- *`R` is not hyperlinear.* By clause 1 of `mf-nonhyperlinear-collapse-structure`,
  `R != 1`, so `Res(R) = R != 1`.
- *No nontrivial hyperlinear quotient.* If `rho` is a homomorphism from `R`
  into a hyperlinear group, then `R = Res(R) <= ker rho`, so `rho` is trivial.
- *Finite, amenable, abelian quotients.* Finite and amenable groups are
  hyperlinear, so `R` has no nontrivial finite or amenable quotient. Its
  abelianization is amenable, so `R` is perfect. A proper finite-index
  subgroup would have a proper normal core of finite index, giving a
  nontrivial finite quotient, so there is none.
- *Infinite, no finite normal subgroup.* By clause 2 of
  `mf-nonhyperlinear-collapse-structure` applied to `G`, `R` is infinite.
  Applied to the MF non-hyperlinear group `R`, whose residual is `R`, the same
  clause says `R` has no nontrivial finite normal subgroup.
- *No property (T).* Clause 1 of `kazhdan-mf-hyperlinear-fragment` gives every
  nontrivial property-(T) MF group a nontrivial hyperlinear quotient.
- *Augmentation extends.* If for some injective `u` the assignment `u(g) -> 1`
  did not extend to a character of `C*(u(R))`, then
  `mf-characterless-corona-image-has-hyperlinear-quotient` would give a proper
  normal subgroup `N` of `R` with `R/N` hyperlinear, a nontrivial hyperlinear
  quotient.

**Part 2.** Suppose `G` has property (T). `G/R` is hyperlinear by clause 1 of
`mf-nonhyperlinear-collapse-structure`. Three standard facts, proved inline:

- *Quotients inherit (T).* If `(S, epsilon)` is a Kazhdan pair for `G`, a
  representation of `G/R` with an `(image of S, epsilon)`-almost invariant
  unit vector pulls back to `G` with the same vector. The resulting nonzero
  `G`-invariant vector is `G/R`-invariant.
- *An amenable group with (T) is finite.* If `Q` is amenable with Kazhdan pair
  `(S, epsilon)`, take a Følner set `F` with `|sF delta F|/|F| < epsilon^2`
  for `s` in `S`. The unit vector `xi = 1_F/sqrt|F|` in `l^2(Q)` satisfies
  `||lambda(s) xi - xi||^2 = |sF delta F|/|F|`, so it is almost invariant.
  Property (T) gives a nonzero invariant vector in `l^2(Q)`. It is constant,
  so `Q` is finite.
- *Finite-index subgroups of Kazhdan groups are Kazhdan.* Let `H <= G` have
  index `m`, left transversal `T`, and let `(S, epsilon)` be a Kazhdan pair for
  `G`. Write `s^(-1) t = t(s,t) h(s,t)` with `t(s,t)` in `T` and `h(s,t)` in `H`,
  and put `Q = {h(s,t)}`, a finite set. Let `pi` be a representation of `H` on
  `V` with a `(Q, epsilon)`-almost invariant unit vector `xi`. The induced
  representation acts by `(lambda(s) f)(x) = f(s^(-1) x)` on functions
  `f : G -> V` with `f(xh) = pi(h)^(-1) f(x)`, normed by
  `||f||^2 = sum over t in T of ||f(t)||^2`. The function with
  `f(th) = pi(h)^(-1) xi` has `||f||^2 = m` and

  ```text
  ||lambda(s) f - f||^2 = sum_t ||pi(h(s,t))^(-1) xi - xi||^2 < m epsilon^2.
  ```

  So `f/sqrt(m)` is `(S, epsilon)`-almost invariant, and the induced
  representation has a nonzero `G`-invariant vector `F`. Invariance makes `F`
  constant, say `F = v != 0`, and `F(xh) = pi(h)^(-1) F(x)` gives
  `pi(h) v = v` for every `h`. So `(Q, epsilon)` is a Kazhdan pair for `H`.

Now suppose `G/R` were amenable. It has (T) by the first fact, so it is finite
by the second. So `R` has finite index, and by the third fact `R` has (T). By
part 1 `R` does not have (T), a contradiction. Hence `G/R` is non-amenable, in
particular infinite, and it has (T) by the first fact.

**Part 3.** Let `G` be MF with `G/Res(G)` amenable. If `G` were not
hyperlinear, part 1 would make `Res(G)` a nontrivial MF group with no
nontrivial hyperlinear quotient, against the hypothesis.

**Part 4.** In part 1, replace part 1 of
`hyperlinear-residual-restricts-along-amenable-quotients` by implication
(i) to (ii) of its clause 2, for the class `C` containing `G/R`. The rest of
the argument for part 1 is unchanged.

**Residually finite remark.** If `H` has finite index in `G` and contains `R`,
then by `hyperlinear-visibility-transfers-across-finite-index` an element of
`H` is visible in `H` exactly when it is visible in `G`. With the dictionary
above this gives `Res(H) = Res(G) intersect H = R`. The equivalence with
extension permanence is clause 2 of
`hyperlinear-residual-restricts-along-amenable-quotients`. The sofic failure is
the statement of `sofic-semidirect-product-closure-fails`, which is context
and not used in the parts above.
