---
rg: 2
id: stw99-lxxvi-local-sr1-collapse-criterion
kind: claim
title: One ideal-local cancellation defect repaired to stable rank one by Z refutes LXXVI
artifacts:
  - research/artifacts/stw99-lxxvi-third-depth-audit-2026-08-30.md
---

Let `A` be a separable pure C*-algebra and let `p,q` be projections in
`A tensor K`.  Put `J=Ideal(p,q)`.  Suppose

```text
[p]=[q] in K_0(J),
[p]!=[q] in Cu(A),
stable_rank(J tensor_min Z)=1.
```

Then the first-factor map `Cu(A)->Cu(A tensor_min Z)` is not injective, so
`A` is a counterexample to STW Problem LXXVI.

Only the generated stabilized ideal, rather than all of `A tensor Z`, is
required to have stable rank one.
