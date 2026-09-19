---
rg: 2
id: strict-pauli-ceiling-audits-final-activator
kind: claim
title: The explicit Pauli ceiling closes a genuinely final activator
distinct_from:
  marked-clifford-table-exponential-dimension: that proves the analytic capacity bound; this checks the exact constants, ceiling, recursion quantifiers, and final-presentation meaning needed by the machine compiler.
  dimension-reported-clifford-table-halting-compiler: that asks to construct the activator; this proves that the stated activator interface would suffice but does not construct it.
---

**ESTABLISHED CONDITIONAL THEOREM.**  Suppose a total computable compiler,
before running its source machine `e`, outputs one finite presentation
`P_e`, a word `w_e`, and a computable constant `C_e>0`.  Assume:

1. if `e` does not halt, `w_e` is nontrivial in `P_e`;
2. if `e` halts and reports `D`, then every `D`-dimensional tuple `U` for the
   already fixed presentation decodes an all-pairs map
   `f:E_(N(D))->U(D)` with

```text
eta <= C_e Def_(P_e)(U),
f(J)=w_e(U),
N(D)=ceil(log_2((1764/1763)D)).                         (SPC1)
```

Then the compiler satisfies instance-modulated Kleene soundness with

```text
delta_e=1/(84 C_e),                  alpha_e=1/2.       (SPC2)
```

Consequently, together with the nonhalting clause, the existing
instance-modulated Kleene theorem produces a finitely presented
nonhyperlinear group.  The rational search may use any fixed
`beta in (1/2,sqrt(2))`, in particular `beta=6/5`.

The activator hypothesis is coherent only in the following precise sense:
`P_e`, including its finite universal simulator, is finalized before `e`
runs, and `(SPC1)` is a uniform semantic decoding theorem for that fixed
presentation.  “Activate after halt” means that a halt transcript selects
relations already represented by the simulator; it cannot mean appending
generators or relators.  Moreover `C_e` may depend computably on `e`, but not
on `D`, the runtime, or `N(D)`.  Establishing such a final activator remains
exactly the open HS-PCP/table-compilation problem.

