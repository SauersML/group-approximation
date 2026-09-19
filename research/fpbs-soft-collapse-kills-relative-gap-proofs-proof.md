---
rg: 2
id: fpbs-soft-collapse-kills-relative-gap-proofs-proof
kind: route
title: The unique infinite cluster meets any infinite subgroup in an invariant random set, which cannot be finite and nonempty
target: fpbs-soft-collapse-kills-relative-gap-proofs
requires:
  - fpbs-soft-collapse-iff-invariant-sparse-spines
---

Notation as in the target. `(omega_t)` is a soft collapse family on
`G = Cay(Gamma,S)`, realized on a probability-preserving `Gamma`-system
`(X,mu)`. Equivariance means `omega_t(g.x) = g omega_t(x)` for `g in Gamma`,
where `Gamma` acts on bonds by left multiplication.

## Step 1 (the unique cluster is equivariant and has positive density)

Fix `t > p_c(G)`. By (S4) there is a full-measure `Gamma`-invariant set
`X_0` on which `omega_t(x)` has exactly one infinite cluster `C(x)`. Left
multiplication by `g` maps clusters of `omega_t(x)` bijectively onto clusters
of `g omega_t(x) = omega_t(g.x)`, and it preserves infiniteness. Hence

```text
C(g.x) = g C(x)   for all g in Gamma, x in X_0.
```

Put `theta(t) = mu(o in C)`. By invariance of `mu`, `mu(v in C) = theta(t)`
for every vertex `v`. If `theta(t) = 0`, a countable union shows that
`C(x)` is empty for `mu`-a.e. `x`, which contradicts (S4). So `theta(t) > 0`.

## Step 2 (no finite nonempty invariant subsets of an infinite group)

Let `I <= Gamma` be infinite and `A(x) = C(x) ∩ I`. For `h in I`,
`A(h.x) = hC(x) ∩ I = h(C(x) ∩ I) = h A(x)`, since `hI = I`. So the law of
the random subset `A` of `I` is invariant under left multiplication by `I`.

Suppose `mu(|A| = k) > 0` for some finite `k >= 1`. The function
`c(v) = mu(v in A, |A| = k)` is constant on `I`. For `h in I`,
`hv in A(x)` iff `v in h^(-1)A(x) = A(h^(-1).x)`, and `|A(h^(-1).x)| = |A(x)|`.
So `c(hv) = mu(x : v in A(h^(-1).x), |A(h^(-1).x)| = k) = c(v)`, by
invariance of `mu`. Hence `c(v) = c` for all `v in I`. Summing over `v in I` gives

```text
sum_(v in I) c(v) = E[ |A| ; |A| = k ] = k mu(|A| = k) < infinity.
```

Since `I` is infinite, `c = 0`, so `mu(|A| = k) = 0`. This contradicts the
assumption. Hence `mu(0 < |A| < infinity) = 0`. This is the subgroup version
of Lemma 0 of `fpbs-soft-collapse-iff-invariant-sparse-spines-proof`, proved
directly without the mass-transport principle.

## Step 3 (conclusion)

On `{o in C}` we have `o in A`, because `o = e in I`. So `A` is nonempty and
therefore infinite, a.s. On that event `K_o(omega_t) = C`, so
`|K_o(omega_t) ∩ I| = |A| = infinity`. Thus

```text
mu( |K_o(omega_t) ∩ I| = infinity ) >= theta(t) > 0,   chi^I(omega_t) = infinity.
```

This holds for every `t > p_c(G)`, and `(omega_t)_(t <= p_c)` is Bernoulli by
(S2). So the soft relative threshold is `p_c(G)`. ∎

## Corollary

An argument with inputs (a) and (b) of the target concluding
`chi^I_p < infinity` for some `p > p_c(G)` applies verbatim to the collapse
family. Its inputs of type (a) are properties of the joint law up to `p_c`,
which (S2) makes identical, and its inputs of type (b) are (S1)--(S4). Its
conclusion would contradict Step 3. Invariant sparse spines give such a family
by Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines`, and
Z-quotients with finitely generated kernel give spines by Theorem B there. ∎

## Remark proof (weight tilt)

For a Cayley graph, `tau_p(o,x) = tau_p(x^(-1),o) = tau_p(o,x^(-1))`, using
left invariance by `x^(-1)` and then symmetry. Pair `x` with `x^(-1)` in
`X_p`:
`2 X_p = sum_x tau_p(o,x)(w(x) + w(x^(-1))) >= 2 sum_x tau_p(o,x) sqrt(w(e))`.
Submultiplicativity gives `w(e) <= w(e)^2`, so `w(e) >= 1`, and hence
`X_p >= chi_p`. At `p_c` on a Cayley graph, `chi_(p_c) = infinity` by
sharpness (Aizenman--Barsky, Duminil-Copin--Tassion; the mean-field lower bound
`chi_p >= (p_c - p)^(-1)/C` diverges). ∎
