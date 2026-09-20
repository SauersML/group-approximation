---
rg: 2
id: hrf-alt-persistence-needs-sylow-detours
kind: claim
title: Testing persistence on p-towers requires prime-to-p-index detours first
distinct_from:
  edge-twist-extensions-of-triangle-colimits-moment-test: its transfer statement preserves moments under prime-to-p covers; this identifies the necessary subgroup detours before p-tower tests and refutes the fixed-base pro-p shortcut
artifacts:
  - research/artifacts/hyperbolic-rf-alternatives-2026-09-20.md
---

For a group `G`, prime `p`, trivial coefficients `F_p`, and
`α in H^2(G;F_p)`, the following are equivalent:

1. `α` dies on a finite-index subgroup of `G`.
2. There is a subgroup `H <= G` of index prime to `p` and a finite chain
   `H=H_0 >= H_1 >= ... >= H_r`, each `H_(i+1)` normal of index `p` in
   `H_i`, such that `α` dies on `H_r`.

Restriction to `H` is injective, so a nonzero class stays nonzero through
the first detour. But that detour can create `H^1(-;F_p)` even if
`H^1(G;F_p)=0`. Therefore a trivial pro-`p` completion of one group does
not establish persistence of its degree-two classes.

An explicit calibration is `G=A_5`, `p=2`, and the nonsplit double-cover
class from `SL_2(F_5) -> PSL_2(F_5) ≅ A_5`. Here `H^1(G;F_2)=0`, yet the
class dies on the trivial subgroup. The Sylow detour is
`A_5 >= V_4 >= C_2 >= 1`, with indices `15,2,2`.

**Status:** written proof independently reviewed on 2026-09-20; see
Section 5 of `research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md`.
Elementary and no novelty claimed. It corrects a possible overreading of "only p-covers
matter" in the persistent edge-twist program, and does not settle that program.

Proof: [[hrf-alt-persistence-needs-sylow-detours-proof]].
