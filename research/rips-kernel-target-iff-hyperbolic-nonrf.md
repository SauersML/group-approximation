---
rg: 2
id: rips-kernel-target-iff-hyperbolic-nonrf
kind: claim
title: The finite-quotient-free Rips-kernel target exists exactly when a non-residually-finite hyperbolic group exists
distinct_from:
  rips-kernel-without-finite-quotients: that asks for the exact sequence; this proves that producing one is equivalent to the ordinary hyperbolic residual-finiteness problem and hence is not an independent attack.
  non-residually-finite-hyperbolic-group: that asks for one hyperbolic counterexample; this records the two reductions without deciding their common existence question.
---

The following existential assertions are equivalent.

1. There is a short exact sequence

   ```text
   1 -> N -> G -> Q -> 1
   ```

   in which `G` is word-hyperbolic, `Q` is finitely presented and not
   residually finite, and `N` has no nontrivial finite quotient.
2. There is a word-hyperbolic group that is not residually finite.
