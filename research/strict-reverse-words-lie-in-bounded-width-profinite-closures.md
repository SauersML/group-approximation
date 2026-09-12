---
rg: 2
id: strict-reverse-words-lie-in-bounded-width-profinite-closures
kind: claim
title: Every strict rectangle datum has a reverse word in a bounded-width profinite closure of its forward relators
distinct_from:
  metric-ultraproducts-of-finite-groups-are-surjunctive: that is the metric statement about ultraproducts of finite groups with invariant lengths; this is the equivalent combinatorial statement about one free group per strict datum, with no metric and no ultrafilter.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that makes Gottschalk's conjecture the membership of a reverse word in the normal closure of the forward relators; this relaxes membership to a profinite closure of bounded conjugacy width.
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

**OPEN.** Let `D` be a strict rectangle datum (`surjunctivity-is-axiomatized-by-rectangle-clauses`) and `F` the free
group on its non-identity labels.
- `R_f(D)` is the set of forward relators `x_s x_m x_m'^-1 x_s'^-1`, for `(s,m) T_f (s',m')`.
- `W_r(D)` is the set of reverse words `x_m x_s x_s'^-1 x_m'^-1`, for pairs that are not `T_r`-related.
- `Cons_n^F(X)` is the set of products of at most `n` conjugates of elements of `X^(±1)`.

The claim: there are `n >= 0` and `w` in `W_r(D)` lying in the profinite closure of `Cons_n^F(R_f(D))`.

**Equivalent forms** (artifact, Theorem 1.1).
- `metric-ultraproducts-of-finite-groups-are-surjunctive`, through the two routes
  `metric-ultraproduct-surjunctivity-from-bounded-width-closures` and
  `bounded-width-closures-from-metric-ultraproduct-surjunctivity`, which form an intended equivalence cycle.
- **Finite groups.** For every strict `D` there is `n` such that, in every finite group `H` and for every labelling
  `lambda` in `H`, some reverse word at `lambda` is a product of at most `n` conjugates of forward relators at
  `lambda` and their inverses. Only `D` determines `n`.

**Position.**
- **Kernels.** Let `N` be the normal closure of `R_f(D)` and `N_hat` the union of the closures of `Cons_n^F(R_f)`.
  Then `N ⊆ N_hat ⊆ cl(N)`.
- **The ladder.** Gottschalk's conjecture asks for a reverse word in `N`, this claim asks for one in `N_hat`, and
  `cl(N)` contains one for every strict datum.
- **Reflection.** `N_hat` is the kernel of the largest weakly sofic quotient of `F/N`
  (`weak-sofic-reflection-kernel-is-bounded-width-closure`).

## Attempts

- **Unconditional neighbours.**
  - A reverse word always lies in `cl(N)`, since finite groups are surjunctive.
  - It always lies in the sofic reflection kernel `N_sof ⊇ N_hat`, by Gromov–Weiss and
    `surjunctivity-of-a-local-class-is-reflection-kernel-membership`.
  - The claim needs the smaller kernel.
- **Finite surjunctivity gives no width bound.** Fix a finite quotient `lambda: F -> H`. Surjunctivity of
  `H/<<R_f(lambda)>>` puts some reverse word in the normal closure of `R_f(lambda)`, but its conjugacy width can grow
  with `|H|`. The claim needs one `n` for every `H`.
- **Hamming transports reach only the sofic kernel.** By `hamming-transports-of-weak-sofic-models-are-soficity`,
  counting on finite actions certifies membership in `N_sof`, never in `N_hat`.
- **Where a counterexample lives.**
  - A strict `D` with `W_r(D) ∩ N_hat` empty refutes this claim. Such a `D` is a Gottschalk counterexample whose
    largest weakly sofic quotient still realizes it.
  - Conversely, if the claim holds, every group realizing a strict datum violates Glebsky–Rivera's closure
    condition at some reverse word.
