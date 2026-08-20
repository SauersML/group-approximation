---
rg: 2
id: commuting-automorphism-cocycle-forces-multiplicity-proof
kind: route
title: Factor the stable letters by Schur's lemma and take determinants
target: commuting-automorphism-cocycle-forces-multiplicity
requires: []
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

On the invariant isotypic space `T tensor C^m`, Schur's lemma gives

```text
rho(u)=U_alpha tensor P,
rho(v)=U_beta  tensor Q
```

for multiplicity-space unitaries `P,Q`.  The relation `[u,v]=1` and
`U_alpha U_beta=zeta U_beta U_alpha` imply

```text
P Q = zeta^(-1) Q P.                                    (CAC3)
```

Taking determinants in dimension `m` gives

```text
det(P)det(Q)=zeta^(-m)det(Q)det(P),
```

so `zeta^m=1`.  Since `zeta` has order `r`, this is equivalent to `r|m`.

For the limitation, write a large multiplicity as `m=qr+s` with `0<=s<r`.
Use `q` exact `r`-dimensional Weyl blocks and alter or discard only the final
`s`-dimensional block.  Its contribution to ambient normalized squared HS
error is at most `O(r/m)`.  Thus exact divisibility at fixed `r` supplies no
dimension-independent error floor.

