---
rg: 2
id: weak-sofic-reflection-kernel-is-bounded-width-closure
kind: claim
title: The largest weakly sofic quotient of a finitely presented group is cut out by bounded-width profinite closures of its relators
distinct_from:
  glebsky-rivera-w-sofic-criterion: that decides weak soficity of one quotient F/N through its closure condition; this uses the criterion to name the smallest normal subgroup over a finitely normally generated N whose quotient is weakly sofic.
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

**ESTABLISHED** by `weak-sofic-reflection-kernel-proof`.

Let `F` be a finitely generated free group and `R` a finite subset. Put

```text
N_hat(R) = union over n >= 0 of cl( Cons_n^F(R) ),
```

where `Cons_n^F(R)` is the set of products of at most `n` conjugates of elements of `R^(±1)`, and `cl` is profinite
closure.
- `N_hat(R)` is a normal subgroup containing `<<R>>`.
- `F/N_hat(R)` is weakly sofic.
- Every normal `M ⊇ R` with `F/M` weakly sofic contains `N_hat(R)`.

So `F/N_hat(R)` is the largest weakly sofic quotient of `F/<<R>>`, and
`<<R>> ⊆ N_hat(R) ⊆ cl(<<R>>)`.

**Use.** Applied to the forward relators of a strict rectangle datum, it identifies the universal test groups of
`metric-ultraproducts-of-finite-groups-are-surjunctive` (artifact, Corollary 2.4).
