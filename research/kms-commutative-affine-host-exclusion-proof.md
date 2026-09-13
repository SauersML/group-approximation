---
rg: 2
id: kms-commutative-affine-host-exclusion-proof
kind: route
title: Diagonalize past the exponential bound, realize the problem in A_p^2 A, and transfer the word problem along the embedding
target: kms-groups-avoid-commutative-algebra-affine-hosts
requires:
  - commutative-algebra-affine-groups-have-polynomial-word-problem
  - kms-hard-fp-rf-groups-lie-in-apapa-variety
artifacts:
  - research/artifacts/solve-kms-self-similar-affine-2026-09-13.md
---

Direct proof (2026-09-13, lane `solve-kms-self-similar-affine`). Let `g(n) = 2^n` and
`F(g)` be as in `commutative-algebra-affine-groups-have-polynomial-word-problem`.

## Step 1: a recursive problem outside F(g)

This is the diagonal argument of Step 1 of `uniform-wp-bound-excludes-bh-targets-proof`,
repeated here with `g(n) = 2^n`.
- Enumerate deterministic machines `M_1, M_2, ...`, and reserve a distinct computably
  coded input `x_(i,c)` for each pair `(i, c)`.
- Put `x` in `X` iff `x = x_(i,c)` and `M_i`, run for `c*g(c*|x|) + c*|x| + c` steps on
  `x`, does not halt accepting.
- `X` is recursive, since the clock is computable.
- If `M_i` decided `X` within `c*g(c*n) + c*n + c`, it would be wrong at `x_(i,c)`. So
  `X` is not in `F(g)`.

## Step 2: realize X in A_p^2 A

`kms-hard-fp-rf-groups-lie-in-apapa-variety` gives a prime `p` and a finitely presented
residually finite `G in A_p^2 A` satisfying `(KMSV1)`: an algorithm for the word
problem of `G` in time `T` yields one for `X` in time `C*T(C*n) + C*n + C`.

## Step 3: transfer along an embedding

- Suppose `φ : G -> Aff_R(S)` is injective, with `R` and `S` as in the statement. Fix
  generators `a_1, ..., a_k` of `G`.
- Let `Γ = <φ(a_1), ..., φ(a_k)>`. It is a finitely generated subgroup of `Aff_R(S)`,
  and `φ(a_i)` is itself a generator of `Γ`.
- A word in the `a_i` is trivial in `G` iff the same word in the `φ(a_i)` is trivial
  in `Γ`, because `φ` is injective.
- By `commutative-algebra-affine-groups-have-polynomial-word-problem` (part 2), the word
  problem of `G` over `{a_i}` is in `F(g)`, say within `C_1*g(C_1*n) + C_1*n + C_1`.
- By `(KMSV1)`, `X` is then decided within
  `C*(C_1*g(C_1*C*n) + C_1*C*n + C_1) + C*n + C`. Since `g` is non-decreasing, this is at
  most `C_2*g(C_2*n) + C_2*n + C_2` with `C_2 = C*C_1 + C + C_1*C`.
- So `X in F(g)`, contradicting Step 1. ∎

## Remark

Step 3 uses nothing about `Aff_R(S)` except the uniform bound. The same argument
excludes `G` from any class whose finitely generated members all have word problem
in `F(2^n)`. The content added here is that affine groups over finitely generated
commutative algebras over finite fields form such a class, including non-reduced
rings and torsion modules, where linearity over a field is unavailable.
