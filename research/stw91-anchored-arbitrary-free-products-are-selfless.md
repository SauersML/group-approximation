---
rg: 2
id: stw91-anchored-arbitrary-free-products-are-selfless
kind: claim
title: One selfless anchor makes an arbitrary reduced free product selfless
distinct_from:
  robert-selfless-free-product-absorption: that is Robert's binary theorem; this closes an arbitrarily large family by finite induction and directed-union permanence.
  stw91-reduced-free-products-preserve-selflessness: that binary theorem requires both factors to be selfless and has no separability assumption; here only one factor is selfless, while every other factor is separable.
  stw91-cograph-products-preserve-selflessness: that graph-product theorem requires every vertex algebra to be exact and selfless; this free-product theorem needs neither condition away from one distinguished vertex.
  stw99-problem-xci-cstar-simple-selfless: that root asks about every C*-simple group; this proves a broad permanence class having one already-selfless free factor.
artifacts:
  - research/artifacts/stw91-anchored-free-product-permanence-audit-2026-08-30.md
---

Let `I` be a nonempty index set and let

```text
((A_i,rho_i))_(i in I)
```

be C*-probability spaces whose states have faithful GNS representations.
Suppose that there is a distinguished `i_0 in I` such that
`(A_(i_0),rho_(i_0))` is selfless, and suppose that `A_i` is separable for
every `i != i_0`.  Then the reduced free product

```text
*_(i in I) (A_i,rho_i)
```

is selfless.  The index set may be uncountable, the anchor may be
nonseparable, and the other factors need not be exact, nuclear, simple, or
selfless.

In particular, let `(G_n)_(n in N)` be a nonempty countable family of
countable discrete groups.  If `C*_r(G_(n_0))` is selfless for one index
`n_0`, then

```text
C*_r(*_(n in N) G_n)
```

is selfless.  Hence the free-product group is C*-simple, and its reduced
algebra has stable rank one, strict comparison by the canonical trace, and a
unique normalized 2-quasitrace.  No hypothesis is placed on the other groups.
