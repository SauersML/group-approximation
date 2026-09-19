---
rg: 2
id: stw91-php-approximately-inner-crossed-products-are-selfless
kind: claim
title: PHP crossed products of simple uniquely tracial algebras by approximately inner actions are selfless
distinct_from:
  stw99-problem-xci-cstar-simple-selfless: that asks whether every C*-simple group's reduced algebra is selfless; this proves a coefficient-crossed-product family under the PHP and approximate-innerness hypotheses.
  ozawa-php-groups-completely-selfless: taking the coefficient algebra to be the scalars recovers Ozawa's scalar PHP family; the present result permits nontrivial simple uniquely tracial coefficients and nontrivial actions.
  gjkepr-php-crossed-product-expectations-are-selfless: that is a relative, coefficient-valued theorem; this converts it into scalar tracial selflessness and all of Robert's regularity consequences.
  complete-selflessness-tensor-permanence: that tensor theorem covers the trivial-action case under different factor hypotheses; this theorem allows every approximately inner action.
artifacts:
  - research/artifacts/stw91-php-crossed-product-selflessness-audit-2026-08-30.md
---

Let `G` be a discrete group with Ozawa's PHP property.  Let `B` be a simple
unital C*-algebra with unique tracial state `tau`, and suppose that
`alpha:G -> Aut(B)` is an action by approximately inner automorphisms.  If

```text
E:B rtimes_(alpha,r) G -> B
```

is the canonical expectation, then

```text
(B rtimes_(alpha,r) G, tau compose E)
```

is a selfless tracial C*-probability space.  Consequently the reduced
crossed product is simple, has stable rank one and strict comparison by
`tau compose E`, and `tau compose E` is its unique tracial state and unique
normalized 2-quasitrace.

In particular, for **every** action of a PHP group `G` on the Jiang--Su
algebra `Z`, the crossed product `(Z rtimes_r G,tau_Z compose E)` is selfless
and has all the preceding regularity properties.  Here no hypothesis on the
action remains, because every automorphism of `Z` is approximately inner.
