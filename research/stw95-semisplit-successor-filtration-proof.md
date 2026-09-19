---
rg: 2
id: stw95-semisplit-successor-filtration-proof
kind: route
title: Tensor cpc sections and assemble purity through the ordinal filtration
target: stw95-semisplit-successor-filtration-reduction
requires:
  - stw95-purity-passes-to-sequential-inductive-limits
artifacts:
  - research/artifacts/stw95-strongly-purely-infinite-cellular-tensor-audit-2026-08-30.md
---

Consider one successor extension

```text
0 -> J_alpha -> J_(alpha+1) --q--> L_alpha -> 0
```

and let `s:L_alpha->J_(alpha+1)` be a cpc section.  The completely bounded
map

```text
P=id-sq:J_(alpha+1)->J_alpha
```

has range in `J_alpha` and restricts to the identity there.  Functoriality
of the minimal operator-space tensor product extends `id_D tensor P` to the
minimal C*-tensor products.  If

```text
x in ker(id_D tensor q),
```

then `x=(id_D tensor P)(x)`, and the latter lies in
`D tensor_min J_alpha` by algebraic density and continuity.  The reverse
inclusion is automatic, and `id_D tensor q` is onto.  Thus the successor
extension remains exact after tensoring by arbitrary `D`.

Run transfinite induction on `alpha`.  At successors, the tensor ideal is
pure by induction, the quotient `D tensor_min L_alpha` is pure by
hypothesis, and extension permanence of purity makes
`D tensor_min J_(alpha+1)` pure.  At a countable-cofinality limit, take a
cofinal sequence; injectivity of minimal tensoring and algebraic density
identify the tensor product with the sequential inductive limit, which is
pure by `stw95-purity-passes-to-sequential-inductive-limits`.  At an
uncountable-cofinality limit, separability of the filtered ideal forces the
filtration to stabilize below the limit: approximate a tail-dense sequence
inside countably many stages and take the supremum of their indices.  The
induction therefore reaches `D tensor_min E`.
