---
rg: 2
id: full-mf-radical-forces-perfect-commutator-bound
kind: claim
title: Full MF radical forces perfectness and a quadratic self-improvement of the generator displacement
distinct_from:
  defect-saturation-full-mf-radical: that constructs one group with full MF radical; this is a structural consequence of the hypothesis for an arbitrary finitely generated group and constructs nothing.
  full-mf-radical-uniform-asymptotic-collapse: that is the qualitative pointwise collapse of asymptotic representations; this is a pointwise algebraic consequence, perfectness, together with an explicit quadratic estimate that holds for every unitary tuple with no collapse hypothesis.
  bounded-relator-area-controls-opnorm-word-defect: that bounds a word defect by relator area for an arbitrary word; this bounds the generator displacement itself, using a commutator expression of the generators and paying a quadratic term.
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `G=<g_1,...,g_m>` be finitely generated with `Res_MF(G)=G`, and for a
unitary tuple `U in U(d)^m` write

```text
D(U)     = max_i ||U_i - I||_op,
Def_R(U) = max_(r in R) ||r(U) - I||_op.
```

Then `G` is perfect.  Fix words `a_(ik),b_(ik) in F_m` with

```text
g_i = prod_(k=1)^(q_i) [a_(ik)(g), b_(ik)(g)],
w_i = x_i^(-1) prod_(k=1)^(q_i) [a_(ik), b_(ik)],
W   = {w_1,...,w_m},
B   = 2 max_i sum_(k=1)^(q_i) |a_(ik)| |b_(ik)|,
```

so that each `w_i` is a relation of `G`.  Then every dimension `d` and every
`U in U(d)^m` satisfy

```text
D(U) <= Def_W(U) + B D(U)^2,                            (Q1)
```

and on the region `D(U) <= 1/(2B)`,

```text
D(U) <= 2 Def_W(U).                                     (Q2)
```

`B` is explicit once the commutator expression is chosen; `(Q1)` and `(Q2)`
use perfectness alone and no compactness.
