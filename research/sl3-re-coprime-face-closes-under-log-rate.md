---
rg: 2
id: sl3-re-coprime-face-closes-under-log-rate
kind: claim
title: No matrix-form relative-embeddability witness of the SL3 pair is coprime-level Lambda-exact with logarithmically compatible defect
distinct_from:
  sl3-re-lambda-exact-coprime-face-is-unfaithful: that asks the same exclusion with NO rate hypothesis and is open (its original route was invalidated by congruence-slot-escapes-ultraproduct-lambda-algebra); this adds the hypothesis eps_k log n_k -> 0 under which the argument is a theorem.
  congruence-slot-escapes-ultraproduct-lambda-algebra: that shows the congruence slot of h is not in pi(Lambda)'' and so pointwise near-containment cannot reach pi(h); this shows that a logarithmic rate of near-containment does reach it, because the slot has a representative of word length O(log n_k).
  odd-congruence-lambda-exact-sector-collapses: that is the commutant collapse with the exact evaluation W = 1 on the coprime sector; this consumes W = 1 and converts it, under the rate hypothesis, into unfaithfulness of relative-embeddability witnesses.
---

Let `Lambda = SL_3(Z) <= Gamma = SL_3(Z[1/p])`, `h = diag(p, 1, p^(-1))`,
and fix a finite symmetric generating set `S` of `Lambda`.  A matrix-form
witness of `RE/C` for the pair (the sufficient form `(CF1)` of
`relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`) is a
regular-trace embedding `pi = prod_U pi_k : Gamma -> prod_U M_(d_k)` with
von Neumann subalgebras `B_k subset M_(d_k)` such that

```text
eps_k := max_(s in S) dist_2(pi_k(s), B_k) -> 0,
|| E_(B_k)(pi_k(a)) ||_2 -> 0   for every a in Gamma \ Lambda.      (LR1)
```

Call it `Lambda`-exact of coprime type at levels `n_k` if `pi_k|_Lambda`
is a genuine representation factoring through `SL_3(Z/n_k)` with
`gcd(n_k, p) = 1`.

**THEOREM.**  No such witness has `eps_k log n_k -> 0`.  Equivalently, a
coprime-level `Lambda`-exact `RE/C` witness of the `SL_3` pair must have
near-containment defect decaying no faster than `1 / log n_k`: the
surviving enemy on this face is a huge coordinate subgroup algebra
`pi_k(Lambda)''` with slow near-containment in `B_k`.

Scope: matrix coordinates and von Neumann `B_k`, as in `(CF1)`; Gao's
Definition 1.1 also allows QWEP coordinates with hyperfinite `B_k`, which
this statement does not address.  The rate hypothesis is not cosmetic:
`congruence-slot-escapes-ultraproduct-lambda-algebra` shows that without it
`pi(h)` is orthogonal to `pi(Lambda)''`, so no pointwise argument can reach
it.
