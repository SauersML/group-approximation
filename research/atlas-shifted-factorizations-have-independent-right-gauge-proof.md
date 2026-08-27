---
rg: 2
id: atlas-shifted-factorizations-have-independent-right-gauge-proof
kind: route
title: Insert independent right-regular commutant unitaries across the fixed shift
target: atlas-shifted-factorizations-have-independent-right-gauge
requires:
  - atlas-a4-packet-centralizer-product-compiler
---

Because `rho` is a regular A8 representation, every

```text
W in rho(A8)'
```

commutes with every left-regular chart matrix, in particular with the fixed
shift `R=rho(r_0)`.  Also

```text
rho(A8)' subseteq rho(<a_j>)' intersection rho(<b_j>)'.
```

Therefore `X_jW_j` and `W_j^-1Y_j` remain in the required two centralizers,
and

```text
(X_jW_j)R(W_j^-1Y_j)
 =X_j R W_jW_j^-1Y_j
 =X_jRY_j
 =U.
```

No equation couples `W_j` to `W_l` for distinct context occurrences, so they
may be chosen independently.  The factor-reversed case is identical after
exchanging the two named subgroup centralizers.  This proves
`(A4-RIGHT-GAUGE)` and the claim.
