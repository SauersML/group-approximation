---
rg: 2
id: qc-qa-graph-gap-from-perfect-completeness-lcs-compiler
kind: route
title: A perfect-completeness LCS compiler names a linear system whose CFI graphs are qc- but not qa-isomorphic
target: qc-isomorphic-not-qa-isomorphic-graph-pair-exists
requires:
  - perfect-completeness-constant-soundness-lcs-compiler
  - re-oriented-lcs-compiler-gives-nonhyperlinear-group
  - lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
---

Assume a compiler `M -> L_M` satisfying `(PC1)` and `(PC2)` of
`perfect-completeness-constant-soundness-lcs-compiler`.

**Step 1: name one linear system.**  The fixed point of
`re-oriented-lcs-compiler-gives-nonhyperlinear-group` names a nonhalting
machine `M_*` whose linear system `L_* = (A,b)` has `J != 1` in its solution
group `Gamma` and satisfies `omega_q(L_*) < 1`.

**Step 2: `L_*` is tracially satisfiable.**
- Its BCS algebra is `C Gamma / <J = -1>` (Paddock--Slofstra, arXiv:2310.07901v2,
  Example 3.9).
- `J` is a central involution different from `1`.  So `p = (1-J)/2` is a
  central projection with regular trace `tau_reg(p) = 1/2`.
- `x |-> 2 tau_reg(p x)` is a tracial state on `p C Gamma`, which is
  `C Gamma / <J = -1>`.

**Step 3: `L_*` is not `R^U`-satisfiable.**  A *-homomorphism into `R^U` is a
perfect quantum-approximable strategy (Paddock--Slofstra Theorem 3.11(3)).
Such a strategy is a limit of finite-dimensional strategies whose values tend
to one, so it would force `omega_q(L_*) = 1`.

**Step 4: transfer.**  `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap` turns
Steps 2 and 3 into `G_(A,b) ≅_qc G_(A,0)` with `G_(A,b)` not `qa`-isomorphic
to `G_(A,0)`.

The first requirement is goal-equivalent by `lcs-compiler-target-is-goal-equivalent`.
So this route records that the linear-system arm of the graph-pair problem is
the goal itself.  The graph-pair problem may also be reached from sources that
are not linear systems.
