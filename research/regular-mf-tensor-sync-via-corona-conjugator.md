---
rg: 2
id: regular-mf-tensor-sync-via-corona-conjugator
kind: route
title: Package the tensor model as a corona conjugator and apply the general HNN permanence
target: regular-mf-tensor-sync-proves-twisted-rope-mf
requires:
  - twisted-hnn-mf-permanence-with-corona-conjugator
artifacts:
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
---

Second, independently verified proof of the tensor-sync theorem.  From the
hypotheses `(RTS1)`-`(RTS2)`: equality of the two finite edge kernels makes
the two edge restrictions of the left regular representation of the finite
image `G_n` unitarily conjugate by some `W_n`; in the norm reduced product
`E = prod_n (A tensor M_{|G_n|}) / sum_n`, the tuple `V(g,q) = [rho(g)
tensor L_n(lambda_n g, beta_n q)]` and `W = [1 tensor W_n]` satisfy the
edge conjugation exactly, and the ultralimit trace of `tr tensor tr_n` is
the regular character of `Gamma times Q` (the `rho` factor kills `g != 1`;
eventual separation kills `q != 1`).  The separable subalgebra `A' =
C*(V(Gamma times Q), W)` of `E` is MF with the regular tracial state, and
any corona embedding of `A'` carries `W` to an exact conjugator for the
twisted edge.  Now [[twisted-hnn-mf-permanence-with-corona-conjugator]]
applied to the base `Gamma times Q`, `S times 1`, and `theta(s,1) =
(s, tau(s))` yields the regular operator-MF realization of the twisted rope
`R`.  This route replaces the reduced von Neumann HNN normal form of the
original proof by the left-regular-representation argument, and makes the
non-faithfulness of the concrete tensor model harmless by design (artifact
Section 3.4).
