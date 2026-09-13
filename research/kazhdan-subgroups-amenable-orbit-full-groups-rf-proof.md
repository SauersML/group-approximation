---
rg: 2
id: kazhdan-subgroups-amenable-orbit-full-groups-rf-proof
kind: route
title: Følner indicator vectors on the orbit-fibred space are almost invariant, and invariant vectors live on finite orbits
target: kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf
requires: []
---

Write `g` for `rho(g)`. Discard a null set so that `X = X_free`.

**Step 0: cocycle identity.** At free points `c_(gh)(y) = c_g(hy) c_h(y)`,
because `gh(y) = c_g(hy) c_h(y) y` and stabilizers are trivial.

**Step 1: the set of infinite orbits.** Let `Y = {x : Gamma x is infinite}`. It
is Borel, since `Gamma` is countable, and it is `Gamma`-invariant. Suppose, for a
contradiction, that `mu(Y) > 0`.

**Step 2: a unitary representation.** Put

```text
Z = {(x, lambda) ∈ X × Lambda : lambda x ∈ Y},    m = mu × counting,
g.(x, lambda) = (x, c_g(lambda x) lambda).
```

- *It maps `Z` to `Z`:* `g(lambda x) = c_g(lambda x) lambda x` lies in `Y`, which is
  invariant.
- *It is an action:* by Step 0,
  `g.(h.(x, lambda)) = (x, c_g(h lambda x) c_h(lambda x) lambda) = (x, c_(gh)(lambda x) lambda)`.
- *Each `g` is a bijection of each fibre `Z_x = {lambda : lambda x ∈ Y}`:* freeness
  makes `lambda -> lambda x` a bijection of `Z_x` onto `Y ∩ Lambda x`, and there `g`
  acts as the bijection `y -> g y`.

So each `g` is a Borel bijection of `Z` preserving `m`, and
`(pi(g) f)(z) = f(g^-1 . z)` is a unitary representation of `Gamma` on `L^2(Z, m)`.

**Step 3: almost invariant vectors.** `Gamma` is finitely generated, because it
has property (T); let `S` be a finite generating set, and let `E ⊆ Lambda` be the
union of the finite ranges of `c_s` for `s` in `S`. For a finite `Q ⊆ Lambda` put
`A_Q = Z ∩ (X × Q)` and `xi_Q = 1_(A_Q)`. Invariance of `mu` gives

```text
||xi_Q||^2 = sum_(lambda ∈ Q) mu(lambda^-1 Y) = |Q| mu(Y).
```

For `s` in `S`, `pi(s) xi_Q = 1_(s . A_Q)`, and `m(s . A_Q) = m(A_Q)`, so

```text
||pi(s) xi_Q - xi_Q||^2 = m(s.A_Q Δ A_Q) = 2 m(s.A_Q \ A_Q).
```

A point of `s.A_Q \ A_Q` has the form `(x, c_s(lambda x) lambda)` with `lambda` in
`Q` and `c_s(lambda x) lambda ∉ Q`, so `lambda` lies in
`B_Q = {lambda ∈ Q : E lambda ⊄ Q}`. Integrating over `x`,

```text
||pi(s) xi_Q - xi_Q||^2 / ||xi_Q||^2 <= 2 |B_Q| / (|Q| mu(Y)) <= 2 sum_(e ∈ E) |eQ \ Q| / (|Q| mu(Y)).
```

Along a Følner sequence for `Lambda` the right side tends to `0`. So `pi` has
almost invariant vectors.

**Step 4: invariant vectors vanish.** Property (T) gives a nonzero
`pi(Gamma)`-invariant `eta` in `L^2(Z, m)`. For each `g`, `eta(g . z) = eta(z)` for
`m`-almost every `z`. Since `Gamma` is countable and `m` is a product with counting
measure, there is a conull set of `x` such that, for every `g` and every `lambda`
in `Z_x`,

```text
eta(x, c_g(lambda x) lambda) = eta(x, lambda),     and    sum_(lambda ∈ Z_x) |eta(x, lambda)|^2 < ∞.
```

Transport `eta(x, .)` to `Y ∩ Lambda x` through `lambda -> lambda x`. It becomes a
square-summable function that is constant on `Gamma`-orbits, and every such orbit
is infinite because it lies in `Y`. So it vanishes. Hence `eta = 0` almost
everywhere, a contradiction. Therefore `mu(Y) = 0`. ∎

**Consequence 1.** Let `g != 1`. The set of points with finite orbit that `g`
moves has measure `mu(X \ Fix g) > 0`, so it contains some `x`. The action of
`Gamma` on the finite set `Gamma x` is a homomorphism to a finite symmetric group
in which `g` is nontrivial. So `Gamma` is residually finite.

**Consequence 2.** An infinite simple group acts trivially on each finite orbit,
since the kernel of the action is a normal subgroup of finite index. So almost
every point is fixed by all of `Gamma`.

**Consequence 3.** A continuous cocycle on compact `X` has finite range, so
`[[Lambda ~ X]] ≤ W(Lambda ~ X)`. A nontrivial element of `[[Lambda ~ X]]` moves a
nonempty open set, which has positive measure by full support. Apply
Consequences 1 and 2 to the inclusion of the subgroup. ∎

**Hypothesis checks.**
- *Essential freeness* is used in Step 0 and to make fibres bijective in Step 2.
- *The invariant measure* is used for `||xi_Q||^2 = |Q| mu(Y)`: without it the
  boundary estimate cannot be normalized, which is exactly the compressible
  case of `amenable-full-group-forces-invariant-measure`.
- *(T) is necessary:* `Lambda` itself realizes infinite orbits.
