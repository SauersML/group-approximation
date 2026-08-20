---
rg: 2
id: c18-child-oriented-gates-follow-the-two-source-words
kind: claim
title: C18 residual occurrences can be attached to the two literal recurrence children
artifacts:
  - experiments/fanizza_child_oriented_c18_exit_compiler.py
distinct_from:
  oriented-c18-rank-gates-give-branch-balance: that establishes the scalar residual ledger; this identifies each occurrence with one of the two actual source projection words and gives the smaller packet sizes.
  product-clock-synchronizes-fanizza-and-e5: that moves an already chosen frame through the common clock; this supplies the child-specific frames to be moved.
---

On the phase-even C18 carrier define

```text
e_p=p(1-r),             e_q=q((1-r) or p).
```

Their pointwise sum is the positive integer residual multiplicity
`e_1+e_2`, with `e_p<=p` and `e_q<=q`.  Hence the first gate can be based on
the literal Fanizza child `P_tilde_n`, and the second on its literal conjugate
`X_tilde_n P_tilde_n X_tilde_n`; no post-hoc assignment of an anonymous
violation block to a source child is needed.

The two predicates have 8 and 12 atoms.  Their optimized OBDD Schur matrices
have sizes 9 and 10, and every one of the 20 atoms admits a weight-at-most-two
source-fixed frame with the common symmetric kernel, the single hard form
`e_02^*`, and reverse sign `J=+1`.

This eliminates the finite child-label ambiguity in the active/exit split.
It does not yet prove that the active halves of the two child transports land
as a single next-level carrier; that is the remaining multiplicity-return
placement theorem.
