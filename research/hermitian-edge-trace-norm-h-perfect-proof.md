---
rg: 2
id: hermitian-edge-trace-norm-h-perfect-proof
kind: route
title: Theorem 5(b) of the K4-free h-perfect proof, fed with the uniform clique inequality for every m
target: hermitian-edge-trace-norm-h-perfect
requires:
  - hermitian-edge-trace-norm-k4-free-h-perfect
  - hermitian-edge-trace-norm-clique-inequality
artifacts:
  - research/hermitian-edge-trace-norm-k4-free-h-perfect-proof.md
  - research/hermitian-edge-trace-norm-clique-inequality-by-size.md
---

Unreviewed, not Lean-verified. Lane w6-078, 2026-09-18.

**Proof.** Theorem 5(b) of `hermitian-edge-trace-norm-k4-free-h-perfect-proof` says the following:
if `G` is h-perfect and the uniform clique inequality `||C||_1 >= sqrt3 (s - 1)` holds for admissible
`C` on `K_s` for every `s <= omega(G)`, then (**) holds for `G`, for every `w` and every admissible `C`.

Its proof uses Lemma 0' there, and shows that the threshold vector `z = y_+` of a dual `Q` lies in
`STAB(G)`, in three steps.
- *Clique inequalities.* These follow from the uniform clique inequality for `K_|U|`, applied to the
  principal submatrix on `U = K ∩ T(y)`, together with Lemma 0(a).
- *Induced odd holes.* These follow from Lemma 3 there, which rests on the exact odd-cycle bound.
- *All other odd cycles.* These follow by chord splitting (Lemma 4 there).

Since `G` is h-perfect, these inequalities cut out `STAB(G)`.

The uniform clique inequality holds for every `s` by `hermitian-edge-trace-norm-clique-inequality`
(route `hermitian-edge-trace-norm-clique-inequality-by-size`). ∎

**Scope.** Perfect graphs, t-perfect graphs and h-perfect graphs are covered. A graph whose stable
set polytope has other facets (for example odd antiholes `C_7^c`, or webs) is not covered. For such a
graph, (**) reduces to those facets by `hermitian-edge-trace-norm-via-stab-facets`.
