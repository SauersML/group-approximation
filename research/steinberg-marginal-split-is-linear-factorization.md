---
rg: 2
id: steinberg-marginal-split-is-linear-factorization
kind: claim
title: The two Steinberg marginal holes are a factorization and a left-inverse problem
artifacts:
  - research/steinberg-marginal-linear-factorization-proof.md
distinct_from:
  steinberg-fox-recurrence-forces-zero-marginals: this identifies the exact linear certificate for that open implication but does not construct it.
  steinberg-zero-marginal-fox-recurrence-is-zero: this identifies the exact stacked left inverse for that open implication but does not construct it.
---

**ESTABLISHED EQUIVALENCE.**  Let `V=F_p^(F_p^3)`, let

```text
R:V -> V direct_sum V,        R(f)=(X_ch f,Y_ch f),
M:V -> F_p^(F_p^2) direct_sum F_p^(F_p^2),
                              M(f)=(P_f,H_f).          (SML1)
```

Here the chord rows include their linear tree-cut substitutions.  Then:

1. `steinberg-fox-recurrence-forces-zero-marginals` is equivalent to a
   factorization `M=L R` for some linear `L`.
2. `steinberg-zero-marginal-fox-recurrence-is-zero` is equivalent to the
   stacked map `(R,M)` having a left inverse.
3. The conjunction of those two certificates is equivalent to `R` having a
   left inverse, hence to the chord recurrence having only the zero solution.

DERIVATION
steinberg-marginal-linear-factorization-proof
