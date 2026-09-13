---
rg: 2
id: nonaugmentation-rank-function-from-a-discrete-rank-model
kind: route
title: Pull back a nonaugmentation rank function with values in (1/N)Z from a matrix host over a division ring
target: binary-leavitt-units-carry-nonaugmentation-rank-function
requires: []
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**REFUTED ROUTE.**

**The route.**
- Find a nontrivial homomorphism `ρ : L_(F_2)(1,2)^x -> GL_n(D)` for a division ring `D` of characteristic 2.
- Put `rk(X) = rank_D(ρ(X))/n` on matrices over `F_2[R^x]`. This is a Sylvester matrix rank function, and
  `rk(1 - [x]) > 0` whenever `ρ(x) ≠ 1`, so `rk ≠ rk_ε`.
- More generally, look for any nonaugmentation rank function with values in some `(1/N)Z`.

**Where it dies.** `leavitt-unit-hosts-need-nilpotents-of-unbounded-index`.
- There is no nontrivial `ρ` into `GL_n(D)` (Theorem A).
- Every nonaugmentation Sylvester rank function on `F_2[R^x]` takes infinitely many values (Corollary A.2), so no
  such rank function lies in any `(1/N)Z`.
