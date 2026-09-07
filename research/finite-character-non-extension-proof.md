---
rg: 2
id: finite-character-non-extension-proof
kind: route
title: Every character kills the elementary subgroup, but the component character sees the witness
target: finite-character-fails-to-extend-after-stabilization
requires:
  - simple-ah-witness-is-elementary-in-rank-two
  - unit-abelianization-to-algebraic-k1-not-injective
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

## Proof

**Characters kill `E_2` when `2` is invertible.**  Conjugating by
`diag(2,1)` sends `e_12(a)` to `e_12(2a)`, so

```text
[diag(2,1), e_12(a)] = e_12(2a)e_12(-a) = e_12(a),
```

and symmetrically `[diag(1,2), e_21(a)] = e_21(a)`.  So every elementary
generator is a commutator in `GL_2` and any homomorphism to an abelian group
kills `E_2`.

**The witness.**  Let `A` and `v` be as in the prerequisites, so
`diag(v,1_A) in E_2(A)` and the component character `chi_A : A^x -> C_2`,
which exists and is nontrivial on `v` by
`unit-abelianization-to-algebraic-k1-not-injective`.

**The countable ring.**  Let `S_0` be a countable unital `Q`-subalgebra of
`A` containing `v`, `v^(-1)` and the finitely many coefficients of the
elementary factorization of `diag(v,1_A)`.  Enlarge it in countably many
steps: at each stage, for every nonzero `a` already present, adjoin finitely
many elements of `A` witnessing `1 in AaA`, which exist because `A` is
simple.  The union `S` is a countable unital `Q`-algebra in which every
nonzero element generates the unit ideal, so `S` is simple, and it is stably
finite as a subring of a stably finite algebra.  By construction
`v in S^x` and `diag(v,1) in E_2(S)`.

**Conclusion.**  Put `chi = chi_A|_(S^x)`, which is onto `C_2` since
`chi_A(v) != 1`.  If `chi` extended to `chi~ : GL_2(S) -> C_2`, then
`chi~(diag(v,1)) = chi(v) != 1` while `diag(v,1) in E_2(S)` forces
`chi~(diag(v,1)) = 1`, since `2` is invertible in the `Q`-algebra `S`.
