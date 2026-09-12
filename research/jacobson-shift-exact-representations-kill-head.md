---
rg: 2
id: jacobson-shift-exact-representations-kill-head
kind: claim
title: Every exact finite-dimensional representation of the recursive Jacobson candidate kills its head
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that concerns the full elementary group over the Jacobson ring; this proves collapse in the separately presented stable-letter candidate without identifying it with that group.
  conjugate-commuting-perfect-copies-force-exponential-dimension: that is a general exact dimension estimate; this verifies the recursive centralization hypotheses from the seven stable-letter equations and the actual finite packets.
artifacts:
  - research/artifacts/jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md
---

Every exact homomorphism `Theta_shift -> U(d)`, for every finite `d`,
kills the entire head group `G_Q=GL_3(F_2)`. The head transvection
`w=x_13,Q` nevertheless remains nonidentity in the literal bilateral
action of this presentation.

Let `H` be the image of the original generators in `Theta_shift`
and `alpha=Ad_t`. Its finite packets and stable-letter equations give

```text
alpha(H)<=H,               [G_Q,alpha(H)]=1.
```

Consequently the subgroups `alpha^i(G_Q)`, for all `i>=0`, are
pairwise commuting and conjugate. The head group is perfect, by
the elementary identities `x_ij=[x_ik,x_kj]`. If `n` commuting
perfect finite-group factors all act nontrivially on `C^d`, tensor
decomposition gives `d>=2n`. Conjugacy makes every head nontrivial
whenever the first survives, which contradicts this bound for large `n`.

This is exact representation collapse only. The number of heads used
depends on `d`, and the argument does not prove the positive matrix
gap required to exclude arbitrary norm-corona representations.

DERIVATION
jacobson-shift-commuting-heads-dimension-proof
