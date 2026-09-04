---
rg: 2
id: stw99-problem-l-explicit-automorphism-loops
kind: claim
title: Exhibit explicit generators of the fundamental group of Aut of the irrational rotation algebra (STW Problem L)
root: true
artifacts:
  - research/artifacts/stw99-actions-classification-cluster-2026-08-30.md
  - research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md
---

**Problem L of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Find
explicit loops generating `π_1(Aut(A_θ)) ≅ Z^6` (Gabe--Schafhauser in
progress, via the finite analogue of Dadarlat's
`π_k(Aut) ≅ KK^1(C_u A, S^k A)`), or of the matching UCT Kirchberg
algebra; more generally explicit `π_1(Aut(A))` generators for
UCT-Kirchberg or monotracial classifiable `A`.  STW: the rotation
action `T^2 ↷ A_θ` gives an injective `Z^2` (winding numbers through
`tr ∘ Bott ∘ ev`), now proved below to be a direct summand; the other four
generators are not constructed here.

## Proved subsidiary question (2026-09-04)

`stw50-rotation-loops-form-a-direct-summand` proves the direct-summand
assertion explicitly raised by STW immediately before Problem L.
For an automorphism loop alpha, evaluate at U and V, translate both
unitary loops to basepoint 1, apply stabilized Bott, and extract the
coefficient of [1] in K_0(A_theta). The resulting homomorphism to Z^2
is a left inverse to the canonical rotation loops. The argument also
works on A_theta tensor O_infinity.

This settles the subsidiary splitting question. It does not produce
all six loops, so the full Problem L remains open. If the Z^6
computation reported by STW is used, the retraction identifies a
complement isomorphic to Z^4.

## Attempts

The remaining task is to construct four explicit loops generating the
kernel of the retraction. A candidate loop can be placed in that kernel
by subtracting its two rotation coordinates; this gives a concrete
normalization but does not prove generation.

The previous inner-loop bookkeeping was speculative: a map from inner
loops into pi_1(Aut(A_theta)) need not be injective, so its domain rank
cannot be counted as a new independent generator. Similarly, conjugating
by an SL_2(Z) symmetry does not by itself construct a based loop or
compute its integral homotopy class.

The graph/groupoid strategy proposed by STW for the Kirchberg counterpart
remains a route to investigate. It requires actual automorphism loops
and a proof that their homotopy classes form a basis of the remaining
kernel; a rank count or a list of abstract KK classes is insufficient.
