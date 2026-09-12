---
rg: 2
id: stw99-problem-xcv-cu-z-tensor
kind: claim
title: Two C*-algebras with Cuntz semigroup Cu(Z) again have tensor product Cuntz semigroup Cu(Z) (STW Problem XCV, first part)
root: true
refuted_by:
  - stw95-cu-z-tensor-counterexample
distinct_from:
  stw99-problem-xcv-pure-tensor-permanence: that asks only whether pureness survives minimal tensor products; this stronger assertion also demands that no odd K-theory cross class create a new compact Cuntz element.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw95-formalization-boundary-2026-08-30.md
---

**Problem XCV, first part, of Schafhauser--Tikuisis--White, *Nuclear
C\*-algebras: 99 problems*, arXiv:2506.10902v2.**  Is it true that

```text
Cu(A) ~= Cu(Z),  Cu(B) ~= Cu(Z)
        ==> Cu(A tensor_min B) ~= Cu(Z)?
```

The answer is **no**.  The counterexample
`stw95-cu-z-tensor-counterexample` can be chosen separable, unital, simple,
nuclear, UCT, and Z-stable.  Each factor's ordinary Cuntz semigroup forgets
its odd `K_1=Z`, while the external `K_1 tensor K_1` class becomes a second
compact `K_0` direction in the tensor square.
