---
rg: 2
id: free-coset-swap-zero-bias-proof
kind: route
title: Read the fold as the product of two distinct free binary lamps
target: free-coset-swap-factor-has-zero-second-fold-bias
requires:
  - arithmetic-double-swap-extension-is-binary-coset-wreath
---

The coset-wreath normal form identifies `s` and `hsh^(-1)` with the free
binary lamp generators at `C` and `hC`.  Since the cosets are distinct,
`V=hsh^(-1)s` is cyclically reduced of infinite order in their copy of
`C_2*C_2`; hence every nonzero power has canonical group trace zero.
The actor restriction is canonical and `s` is nontrivial, so its trace is
zero as well.  Substitution in the exact two-projection identity

```text
tau(QPQ-(QPQ)^2)=(1/16)(1-Re tau(V^2))
```

gives `1/16`.
