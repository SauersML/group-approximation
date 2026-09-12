---
rg: 2
id: swap-group-cylinder-lift-trees-halve-but-never-refine
kind: claim
title: Swap-group lifts of cylinder projections halve exactly at every cylinder but never refine, in every nontrivial char-2 rank model of the Leavitt units
distinct_from:
  covariant-monotone-cylinder-families-in-rank-models-are-constant: that shows covariant refinement-monotone ideal families are constant; this exhibits a covariant tree of idempotents with exact halving between depths and measures why it does not refine.
  binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap: that lifts the depth-one matrix units through the swap group with a kernel gap; this transports the symmetric split to every cylinder and bounds the refinement gap in every rank model.
  leavitt-two-root-defect-piece-forces-covariant-diagonal: that asks for a covariant orthogonal diagonal from a nonzero defect; this shows the natural torsion lifts halve exactly but their halves are never the next depth's pieces, with no defect input.
artifacts:
  - research/artifacts/defect-piece-covariance-letterwise-firewall-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-defect-cov`; verification requested from `w4-vf-gate`) by
`swap-group-cylinder-lift-trees-proof`.

**Setting.** `R = L_(F_2)(1,2)`, `G = R^x`, `sigma` a nontrivial rank model of `G` over a field of
characteristic two, `sigma~` its linear extension to `F_2[G]`. Put `u = 1 + s_0 t_1`, `v = 1 + s_1 t_0`,
`c = vu`, `e = 1 + [c] + [c^2]`, `p_0 = 1 + [u] + [v] + [uv]`, `p_1 = 1 + [u] + [v] + [vu]`. For a proper
cylinder `w`: `E_w = sigma~(iota_w(1 + e))` and `A_(wi) = sigma~(iota_w(p_i))`.

**Theorem.**
1. `E_w = A_(w0) + A_(w1)` with `A_(w0)`, `A_(w1)` orthogonal idempotents, and all three are covariant under
   prefix replacements.
2. `rk(E_w) = eps > 0` for every proper `w`, and `rk(A_(wi)) = eps/2`.
3. `A_(wi)` and `E_(wi)` both lift `1_[wi]`, but `rk(A_(wi) - E_(wi)) >= eps/2`. The difference is `sigma~` of
   an element of the evaluation kernel.

**Consequence.** Exact rank halving between depths exists for pieces built from torsion, but the halves are
not the covariant pieces at the next depth, so the tree never refines to a diagonal. Its inputs are finite
group relations and letterwise covariance, which
`binary-locally-finite-hnn-models-violate-two-root-identity` shows cannot force the gate.

## Attempts

- 2026-09-12 `w4-defect-cov`: proved; artifact Section 3.
