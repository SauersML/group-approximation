---
rg: 2
id: mf-kazhdan-nsp-hyperlinear-via-residual-proof
kind: route
title: Force the hyperlinear residual to finite index, run the Kazhdan fragment there, and induce back
target: mf-kazhdan-groups-with-normal-subgroup-property-are-hyperlinear
requires:
  - mf-nonhyperlinear-collapse-structure
  - mf-finite-normal-tracially-visible
  - kazhdan-mf-hyperlinear-fragment
  - hyperlinear-elementwise-visibility
  - hyperlinear-visibility-transfers-across-finite-index
---

## Why sufficient

*Part 1.* Suppose `G` is MF, has the normal subgroup property and satisfies
the hypothesis of part 1, but is not hyperlinear. Let `R` be the hyperlinear
residual of `G`, the intersection of the kernels of all homomorphisms from
`G` into hyperlinear groups. `R` is a normal subgroup. By `(S1)` of
`mf-nonhyperlinear-collapse-structure`, `R != 1` and its nontrivial elements
are exactly the elements of `G` that are not tracially visible.

*`R` is not finite.* If it were, `R` would be a nontrivial finite normal
subgroup of the MF group `G`. By `mf-finite-normal-tracially-visible` every
nontrivial element of `R` would then be tracially visible, contradicting
`(S1)`. So `R` is infinite, and by the normal subgroup property it has finite
index `m`.

*An element of `R` is visible in `R`.* By hypothesis `R` has a surjection
`rho : R -> Q` onto a nontrivial hyperlinear group. Pick `g in R` with
`rho(g) != 1`. The necessity half of `hyperlinear-elementwise-visibility`
makes `rho(g)` tracially visible in `Q`. Composing models of `Q` with `rho`
keeps defects and traces, so `g` is tracially visible in `R`.

*Contradiction.* By part 2 of
`hyperlinear-visibility-transfers-across-finite-index`, `g` is tracially
visible in `G`. But `g` is a nontrivial element of `R`, which contradicts
`(S1)`. Hence `G` is hyperlinear.

*Part 2.* Let `G` have property (T) and let `R` be a nontrivial finite-index
normal subgroup. Two facts give the hypothesis of part 1.

1. `R` is MF: restricting an injective homomorphism from `G` into the unitary
   group of the norm matrix corona to `R` keeps it injective.
2. `R` has property (T), by the lemma below.

Then `kazhdan-mf-hyperlinear-fragment`, clause 1, gives `R` a nontrivial
hyperlinear quotient.

## Lemma: finite-index subgroups of Kazhdan groups are Kazhdan

Let `(S, epsilon)` be a Kazhdan pair for `G`, with `S` finite, and let
`H <= G` have finite index `m`. Choose a transversal `T` of the left cosets,
and write `s^(-1) t = t(s,t) h(s,t)` for `s in S`, `t in T`, as in `(I1)` of
`hyperlinear-visibility-finite-index-induction-proof`. Put
`Q = { h(s,t) : s in S, t in T }`. This is finite. We show `(Q, epsilon)` is a
Kazhdan pair for `H`.

Let `pi` be a unitary representation of `H` on `K`, and `xi` a unit vector
with `||pi(q) xi - xi|| < epsilon` for all `q in Q`. Form the induced
representation on

```text
L = { f : G -> K : f(xh) = pi(h)^(-1) f(x) for all x in G, h in H },
||f||^2 = sum_{t in T} ||f(t)||^2,
```

with `(lambda(x) f)(y) = f(x^(-1) y)`. The norm does not depend on the
transversal, because `pi` is unitary. Each `lambda(x)` permutes the cosets,
so `lambda` is unitary.

Define `f(th) = pi(h)^(-1) xi` for `t in T`, `h in H`. It is well defined and
lies in `L`, with `||f||^2 = m`. For `s in S` and `t in T`,

```text
(lambda(s) f)(t) = f(t(s,t) h(s,t)) = pi(h(s,t))^(-1) xi,
||lambda(s) f - f||^2 = sum_t ||pi(h(s,t))^(-1) xi - xi||^2 < m epsilon^2.
```

So `f/sqrt(m)` is an `(S, epsilon)`-invariant unit vector. Property (T) of
`G` gives a nonzero `lambda(G)`-invariant vector `F in L`. Invariance means
`F(x^(-1) y) = F(y)` for all `x, y`, so `F` is constant, say `F = v`. Now
`v = F(h) = pi(h)^(-1) F(e) = pi(h)^(-1) v` for all `h in H`. Since `F != 0`,
`v != 0`, so `v` is a nonzero `pi(H)`-invariant vector. Hence `(Q, epsilon)`
is a Kazhdan pair for `H`, and `H` has property (T). End proof.
