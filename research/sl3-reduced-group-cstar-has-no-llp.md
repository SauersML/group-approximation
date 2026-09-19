---
rg: 2
id: sl3-reduced-group-cstar-has-no-llp
kind: claim
title: The reduced group C-star algebra of SL_3(Z) does not have LLP
invalidates: [sl3-weak-ucp-via-reduced-llp]
distinct_from:
  sl3-z-weakly-ucp-stable: that is a positive-definite correction statement for prescribed hyperlinear approximations through the full group C-star algebra; failure of reduced LLP neither proves nor refutes it.
  no-published-unconditional-codense-stable-host: that records failure of LLP for the full group C-star algebra and the literature boundary for stable hosts; this closes the separate reduced-algebra shortcut by the canonical trace.
---

**ESTABLISHED.**  Put `G=SL_3(Z)`.  Then

```text
C^*_r(G) does not have Kirchberg's local lifting property.       (RLL1)
```

Indeed, `G` is residually finite, hence hyperlinear, and it is nonamenable.
Apply `llp-regular-dominating-completion-forces-nonhyperlinear` to the left
regular representation `pi=lambda_G`.  Its weak-containment hypothesis is
tautological, while nonamenability of `pi` is equivalent to nonamenability of
`G`.  If `C^*_r(G)=C^*_(lambda_G)(G)` had LLP, that theorem would force `G`
to be nonhyperlinear, contradicting residual finiteness.  Thus `(RLL1)`
holds.

Equivalently, the canonical trace on `C^*_r(G)` is hyperlinear but not
amenable.  LLP would make it amenable by
`llp-makes-hyperlinear-traces-amenable`; amenability of the regular trace is
equivalent to amenability of the group.

This is a route firewall, not a negative result about weak ucp-stability.
A prescribed regular-type hyperlinear approximation does factor through the
reduced norm in the ultraproduct, but it cannot be locally lifted merely by
asserting LLP of the reduced algebra.  Any positive proof of
`sl3-z-weakly-ucp-stable` must use the larger full-norm positive-definite
problem or a sequence-specific rigidity argument.
