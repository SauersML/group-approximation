---
rg: 2
id: conditional-whitehead-quarter-turn-root-kernel-proof
kind: route
title: Compute the conditional Whitehead quarter-turn and retract its split root compiler
target: split-steinberg-conditional-swap-has-root-kernel-countermodel
requires:
  - role-packed-bcs-gap-is-one-idempotent
  - role-packed-forbidden-reflection-is-not-a-group-word
  - orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy
---

Multiply the three elementary matrices in `(SCW2)` using `p^2=p`; this gives
the displayed quarter-turn, its square, and the exact conjugacy
`diag(p,0) -> diag(0,p)`.  Root addition gives `(SCW4)`.  Then kill every
root generator.  Steinberg addition, commutator multiplication, packet
covariance, and stabilized Morita rows all become identities, so the external
structural group is a retract.  Pull back its finite
uniform-assignment/role regular
model.  The aggregate character idempotent has positive trace, the mark is
nontrivial, and the killed quarter-turn fixes the selected seed corner
exactly, proving the zero-escape countermodel.
