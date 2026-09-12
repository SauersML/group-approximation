---
rg: 2
id: common-corner-literal-contexts-bass-serre-proof
kind: route
title: Tensor the selected predicate blocks and pull the virtually-free corner trace back
target: common-corner-literal-contexts-stop-at-bass-serre
requires:
  - every-boolean-predicate-has-a-character-free-finite-type-block
  - bcs-corner-model-is-a-compatible-projection-atlas
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
---

For the positive assertion, tensor the finitely many selected irreducible
predicate blocks.  Primitive central idempotents multiply under finite direct
products, and joint eigenspaces in one tensor factor are amplified, not
changed, by all other factors.  This proves `(LCL1)--(LCL2)`.

For compression rigidity, let `a=(1-q)u q`.  From unitarity of `q u q` in
the corner,

```text
0=q-q u^* q u q=q u^*(1-q)u q=a^*a,
```

hence `a=0`.  The corresponding equation for `u^*` gives
`(1-q)u^*q=0`; taking adjoints gives `q u(1-q)=0`.  Thus `uq=qu`.

Finally `(LCL3)--(LCL4)` are precisely a BCS corner model.  A finite graph
of finite groups has virtually-free fundamental group and hence a
Connes-embeddable canonical trace.  Faithfulness of the canonical trace gives
`tau_Pi(q)>0`, so the normalized corner trace exists and its pullback is a CE
trace on the BCS algebra.  This contradicts the defining no-CE-trace property.

Equivalently, `nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear`
would make `Pi` nonhyperlinear, contradicting virtual freeness.
