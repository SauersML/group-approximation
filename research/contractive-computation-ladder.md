---
rg: 2
id: contractive-computation-ladder
kind: claim
title: Exponential signal contraction against polynomial certificate cost forces a uniform energy floor
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  fractional-source-branch-pressure: that is a Perron-type inequality on carrier masses of a finite branch network; this is a one-dimensional recursion in a computational level index and involves no network.
  bounded-overlap-syndrome-energy-accounting: that sums local charges with bounded incidence into a global energy bound; this iterates a single contraction inequality down a ladder and its convergence comes from exponential decay beating polynomial growth.
---

Let `a_n >= 0` be uniformly bounded and suppose that for a fixed `0 < lambda < 1`,
a fixed polynomial `p`, a constant `C`, and a global normalized-HS relator energy
`E`,

```text
a_n <= lambda a_(n+1) + C p(n) sqrt(E)      for all n >= 0.          (CCL1)
```

Then

```text
a_0 <= C sqrt(E) sum_(n>=0) lambda^n p(n),                           (CCL2)
```

and in particular if marked separation forces `a_0 >= a_* > 0` then

```text
E >= a_*^2 / ( C^2 ( sum_(n>=0) lambda^n p(n) )^2 ) > 0.             (CCL3)
```

**Positive-density version.**  The contraction need not occur at every level.
If a factor `lambda < 1` occurs on a set of levels of lower density `eta > 0`
and the remaining levels have factor one, the product of transfer factors down
to level `N` is at most `lambda^(eta N + o(N))`, the series in `(CCL2)` still
converges, and `(CCL3)` still holds with a larger constant.

**What it does and does not supply.**  This is the precise form of "signal
destruction is exponential while approximation-error accumulation is only
polynomial, so destruction wins".  It is a statement about a ladder that is
assumed to exist: nothing here constructs `a_n` or establishes `(CCL1)` for any
group.  Its value is that it fixes the exchange rate — a certificate cost may
grow polynomially in the level index without breaking the argument, so a
construction is not obliged to keep its per-level bookkeeping bounded.
