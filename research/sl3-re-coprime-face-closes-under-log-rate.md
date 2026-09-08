---
rg: 2
id: sl3-re-coprime-face-closes-under-log-rate
kind: claim
title: No matrix-form relative-embeddability witness of the SL3 pair is coprime-level Lambda-exact with logarithmically compatible defect
distinct_from:
  sl3-re-lambda-exact-coprime-face-is-unfaithful: That now proves the stronger exclusion without a rate hypothesis using uniform Kazhdan carrier containment; this retains the earlier word-length proof under eps_k log n_k -> 0.
  congruence-slot-escapes-ultraproduct-lambda-algebra: That separates the constant-sequence subgroup algebra from the coordinate subgroup algebras; this obtains carrier containment by telescoping a representative of word length O(log n_k).
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

**THEOREM.** No such witness has `eps_k log n_k -> 0`.

This remains a valid weaker theorem. As of 2026-09-08,
`sl3-re-lambda-exact-coprime-face-is-unfaithful` excludes all such
witnesses without any containment-rate condition. Slow containment
is therefore no longer a remaining case on this face.

Scope: matrix coordinates and von Neumann `B_k`, as in `(CF1)`; Gao's
Definition 1.1 also allows QWEP coordinates with hyperfinite `B_k`, which
this statement does not address. The rate hypothesis is needed by this
particular telescoping proof. The later Kazhdan arguments control the
moving slot directly in the coordinate carriers and do not identify it
with an element of `pi(Lambda)''`.
