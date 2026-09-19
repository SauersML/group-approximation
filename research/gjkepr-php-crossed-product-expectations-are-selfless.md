---
rg: 2
id: gjkepr-php-crossed-product-expectations-are-selfless
kind: claim
title: Approximately inner actions of PHP groups have selfless reduced-crossed-product expectations
distinct_from:
  ozawa-php-groups-completely-selfless: Ozawa treats the scalar coefficient algebra and proves complete selflessness of the reduced group algebra; this is relative selflessness of the canonical expectation for arbitrary unital coefficient algebras and approximately inner actions.
  complete-selflessness-tensor-permanence: a trivial action gives a tensor product, but this theorem permits nontrivial approximately inner actions and concerns the coefficient-valued expectation.
  stw99-problem-xci-cstar-simple-selfless: this is a sufficient crossed-product theorem under the PHP and approximate-innerness hypotheses, not the universal assertion for all C*-simple groups.
artifacts:
  - research/artifacts/stw91-php-crossed-product-selflessness-audit-2026-08-30.md
---

Let `G` be a discrete group with Ozawa's PHP property, let `B` be a unital
C*-algebra, and let

```text
alpha:G -> Aut(B)
```

be an action such that every `alpha_g` is approximately inner.  Then the
canonical conditional expectation

```text
E:B rtimes_(alpha,r) G -> B
```

is selfless; equivalently, the operator-valued C*-probability space
`(B rtimes_(alpha,r) G,E,B)` is selfless.  No separability, exactness,
nuclearity, simplicity, trace, or countability hypothesis is imposed on
`B` or `G` beyond the conditions displayed above.

**Established (literature).**  This is Theorem 9.2, introduced as Theorem
1.4, of Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert, *Selfless
C*-correspondences, operator valued C*-probability spaces and completely
positive maps*, arXiv:2607.20361v1 (22 July 2026).  It is imported here, not
reproved.
