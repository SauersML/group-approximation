---
rg: 2
id: infinite-character-actor-fd-proof
kind: route
title: Use finite joint spectrum and exclude every seed-visible finite orbit
target: infinite-character-actor-kills-fd-mark
requires:
  - one-pauli-seed-character-expansion
---

On the negative `J` sector, simultaneous diagonalization of the finite
dimensional commuting involutions `rho(M)` gives the finite set `(ICA3)`.
For `a in A`, conjugation sends the `chi`-eigenspace to the
`a chi`-eigenspace, so the support is invariant.  Condition `(ICA1)` then
puts the whole support in the `+1` face of `m_0`.  The seed commutator says
that `z` exchanges the `+1` and `-1` eigenspaces of `m_0`; since the latter
is zero, the whole marked sector is zero.

For nontriviality, character translation satisfies

```text
T_alpha M_(m) T_alpha^*=alpha(m) M_(m).
```

Taking `m=m_0` and `alpha(m_0)=-1` proves the Pauli relation with `J=-I`.
The Koopman operators implement the semidirect actor covariance.  No trace
is asserted or needed for algebraic nontriviality.
