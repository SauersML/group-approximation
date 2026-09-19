---
rg: 2
id: glue-lemma-holds-for-quadratic-functions
kind: claim
title: For ambient degree at most two the orientation-glue conclusion holds with L = 16/delta and gamma = 1
distinct_from:
  affine-orientation-glue-lemma: that is the general statement for arbitrary bounded f, which is open; this is the special case deg f <= 2, which is proved, and it holds in a strictly stronger form -- gamma = 1, no escape clause, and no dependence on rho, d, alpha or k.
  restricted-influence-transfer-holds-below-degree-three: that is the inequality (T1) and the degree-three obstruction; this is the list-decoding conclusion drawn from it.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Let `f : {-1,1}^Omega -> [-1,1]` with `deg f <= 2`, let
`0 < rho <= 1`, `g = T_rho f`, and let `B subset Omega \ {0}` be **any** set
of directions such that for each `b in B` some coset `C_b = q_b + <b>` is
`(d, delta)`-heavy for `g|_{D_b}`.  Put

```text
Q = { x in Omega : Inf_x(g) >= delta/8 }.
```

Then

```text
|Q| <= 16/delta     and     C_b intersect Q != empty for EVERY b in B.
```

So the conclusion of `affine-orientation-glue-lemma` holds with
`L = 16/delta` and `gamma = 1`.

Three features of this special case are worth reading off, because they say
what the general statement should look like.

* **No escape clause is needed.**  The list `Q` is produced outright.  This
  is direct evidence that the escape clause in the general formulation is
  spurious; see `glue-lemma-escape-clause-voids-the-conclusion`.
* **`gamma = 1`, not merely a constant.**  Every heavy coset is hit, not a
  `gamma`-fraction.  The weakening to a fraction is a concession to the
  unknown regime, not something the low-degree truth requires.
* **No dependence on `rho`, `d`, `alpha` or `k`.**  In particular the
  density hypothesis on `B` is not used at all -- `B` may be a single
  direction or all of `Omega \ {0}`.

The list is exactly the set of ambient influential coordinates, which is
the naive decoder of `glue-lemma-via-ambient-influence-transfer`.  That
route is dead in general, and this claim locates precisely how far it does
survive: to ambient degree two, and no further, by
`restricted-influence-transfer-holds-below-degree-three`.

The proof is `glue-lemma-quadratic-case-proof`.
