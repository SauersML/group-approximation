---
rg: 2
id: no-uniform-metabelian-higman-compiler
kind: claim
title: No total effective Higman compiler preserves metabelianity on every metabelian input
distinct_from:
  lamplighter-fp-amenable-interface-is-directional: that gives one explicit finitely presented metabelian overgroup of one fixed group; this rules out uniform effective selection over arbitrary recursive-presentation indices.
  amenability-of-finite-presentations-is-pi2-complete: that only needs a compiler specialized to one totality family, so this obstruction does not refute the root.
---

**ESTABLISHED.**  There is no total computable operation which, from every
finitely generated recursive presentation `Q=<X|R>`, outputs a finite
presentation `C(Q)` and computable words `iota_Q(x)` inducing an embedding

```text
iota_Q:Q -> C(Q),
```

with the guarantee that `C(Q)` is metabelian whenever `Q` is metabelian.

The conclusion remains true if "metabelian" for the output is weakened to
"residually finite" and the guarantee is required only for abelian inputs.

This is an effectivity obstruction, not a contradiction to the classical
Baumslag--Remeslennikov theorem that each finitely generated metabelian group
embeds in some finitely presented metabelian group.  It also does not rule
out a construction specialized to the shift-RAAG totality family: there the
positive abstract group is always `Z wr Z`, while the index carries the
universal event.

DERIVATION
[[no-uniform-metabelian-higman-compiler-proof]]
