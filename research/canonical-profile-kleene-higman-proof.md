---
rg: 2
id: canonical-profile-kleene-higman-proof
kind: route
title: Enumerate algebra-mark zero proofs, contradict canonical norm, and apply effective Higman
target: canonical-profile-kleene-higman
requires: []
artifacts:
  - research/artifacts/meta-recursive-qca-audit-2026-08-22.md
---

Equality `p_e=0` in the recursively presented group algebra is recursively
enumerable: after clearing denominators, enumerate finite normal-closure
certificates identifying enough support words to make every coefficient class
sum to zero. Construct the machine which computes `(Gamma_e,p_e)` and halts on
the first such certificate. Kleene's recursion theorem supplies a fixed point
`e_*`.

It cannot halt, because the certificate would say `p_(e_*)=0` while `(CPK1)`
would say it is nonzero. Completeness of certificate enumeration also shows
directly that `p_(e_*)!=0`. Thus `(CPK2)` applies.

If `Gamma_(e_*)` were hyperlinear, choose canonical-delta microstates. Then
`(CPK2)` makes `||p_(e_*)(U_n)||_2->0`, while moment convergence on the finite
support of `p^*p` gives

```text
||p_(e_*)(U_n)||_2^2
 -> tau_Gamma(p_(e_*)^*p_(e_*)) > 0,
```

using faithfulness of the canonical group trace on `C[Gamma]`. Contradiction.
The resulting group is finitely generated and recursively presented;
effective Higman embeds it in a finitely presented group. Hyperlinearity
passes to subgroups, so the host is non-hyperlinear.
