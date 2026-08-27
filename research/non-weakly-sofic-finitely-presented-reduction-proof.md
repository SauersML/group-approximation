---
rg: 2
id: non-weakly-sofic-finitely-presented-reduction-proof
kind: route
title: Localize to a finitely generated subgroup, then present on the criterion's finite list
target: non-weakly-sofic-finitely-presented-reduction
requires: [glebsky-rivera-w-sofic-criterion]
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
---

Let `G` be non-weakly-sofic.

**Step 1: normalize the separation constant.**  Suppose `H` is a group with
models of separation `alpha>0`.  Given `Phi` and `eps>0`, take a
`(Phi, alpha*eps, alpha)`-model into `(K,d)` and replace `d` by `d/alpha`,
which is again a bi-invariant metric since the metric is not required to be
normalized.  The result is a `(Phi,eps,1)`-model.  So "weakly sofic" may be
read with the single constant `alpha=1` throughout.

**Step 2: localize.**  Suppose every finitely generated subgroup of `G` were
weakly sofic.  Given finite `Phi subseteq G` and `eps>0`, apply Step 1 inside
`<Phi>` to get a `(Phi,eps,1)`-model.  A model is a map defined on `Phi`
only, so this is a `(Phi,eps,1)`-model for `G`.  Hence `G` would be weakly
sofic, a contradiction.  So some finitely generated `G_0 <= G` is not weakly
sofic.

**Step 3: present.**  Write `G_0 = F/N` with `F` free of finite rank.  By
`glebsky-rivera-w-sofic-criterion` in the contrapositive, there are
`g_1,...,g_k in N` and

```text
x  in  closure_prof([g_1]^F...[g_k]^F)  \  N.
```

Put `N_0 := N(g_1,...,g_k)`.  Then `N_0 subseteq N`, so `x not-in N_0`, while
the closure membership is a statement about `F, x, g_1, ..., g_k` alone and
is untouched by shrinking `N` to `N_0`.  Applying the criterion again, now to
`F/N_0`, the containment fails at the sequence `g_1,...,g_k`, so

```text
< s_1,...,s_r | g_1,...,g_k >
```

is finitely presented and not weakly sofic.

This is Glebsky--Rivera's own proof of their Corollary 4.4, quoted in the
citation route of the criterion; the audit reconstructs it as its Theorem 3.1
`(1) => (3) => (2)`.
