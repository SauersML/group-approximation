---
rg: 2
id: simple-ln-completion-premise-equivalence-proof
kind: route
title: Use the trivial recursion on a simple base, compute the core centralizer by linear independence, and compose Clapham with the finitely presented case
requires:
  - leavitt-nekrashevych-completion-embeds-and-is-fp
  - leavitt-nekrashevych-completion-simplicity-criterion
  - fp-simple-algebras-have-solvable-word-problem
target: simple-ln-completion-premise-is-equivalent-to-algebra-bh
---

Notation as in the claim. `L_d = K<s_1..s_d, t_1..t_d | t_i s_j = δ_ij, Σ_i s_i t_i = 1>`.

## Part 1, (b) ⇒ (a)

This is `algebra-bh-via-simple-leavitt-nekrashevych-completions`. By
`leavitt-nekrashevych-completion-embeds-and-is-fp`, `O_psi` is finitely presented.
By `leavitt-nekrashevych-completion-simplicity-criterion` (part 3) it is simple,
and it contains `A`.

## Part 1, (a) ⇒ (b)

Let `A ≤ S` with `S` finitely presented and simple. Put `B = S` and
`psi(b) = b I_d`, the diagonal matrix. `psi` is a unital injective homomorphism.

**Step 1: `O_psi ≅ S ⊗_K L_d`.** The covariance relation reads
`b = Σ_i s_i b t_i`. Using `t_j s_i = δ_ji`:

```text
t_j b = Σ_i t_j s_i b t_i = b t_j,        b s_k = Σ_i s_i b t_i s_k = s_k b.
```

So in `O_psi` every `b in S` commutes with every `s_i` and `t_i`. Hence `O_psi` is a
quotient of `S *_K L_d` by relations implied by the commutation relations
`[b, s_i] = [b, t_i] = 0`. The quotient of `S *_K L_d` by exactly those commutation
relations is `S ⊗_K L_d`, by the universal property of the tensor product of unital
algebras. So `O_psi` is a quotient of `S ⊗_K L_d`. Conversely, in `S ⊗_K L_d`:

```text
Σ_i (1 ⊗ s_i)(b ⊗ 1)(1 ⊗ t_i) = b ⊗ Σ_i s_i t_i = b ⊗ 1,
```

so the covariance relators hold there. The two maps are mutually inverse on
generators, and `O_psi ≅ S ⊗_K L_d`. The grading of `O_psi` (`deg s = 1`,
`deg t = -1`, `deg S = 0`) is the grading of the second tensor factor, so
`O_k = S ⊗ (L_d)_k` and the core is `C = S ⊗ (L_d)_0`.

**Step 2: minimality.** An ideal `I` of `S` is psi-saturated iff
`I = {b : every entry of b I_d lies in I} = I`. So every ideal is saturated, and
simplicity of `S` gives psi-minimality.

**Step 3: aperiodicity.** Let `k ≠ 0` and let `y in O_k` commute with every element
of `C`. Write `y = Σ_{i=1}^r a_i ⊗ ℓ_i` with `a_1, .., a_r in S` linearly independent
over `K` and `ℓ_i in (L_d)_k`. Every element of a tensor product has such an
expression. For `c in (L_d)_0`, `1 ⊗ c in C`, so

```text
0 = [1 ⊗ c, y] = Σ_i a_i ⊗ [c, ℓ_i].
```

Since the `a_i` are linearly independent, `[c, ℓ_i] = 0` for all `i` and all
`c in (L_d)_0`. So each `ℓ_i` is an element of `(L_d)_k`, `k ≠ 0`, commuting with
the core of `L_d`. By `leavitt-nekrashevych-completion-simplicity-criterion`
(part 4, the Leavitt calibration `B = K`, `psi(λ) = λ I_d`, which is aperiodic),
`ℓ_i = 0`. So `y = 0`, and `(S, psi)` is aperiodic.

**Step 4: embedding.** `psi` is injective, so `S -> O_psi` is injective by
`leavitt-nekrashevych-completion-embeds-and-is-fp` (part 2). So `A ≤ S ≤ O_psi`.

Taken together, `B = S`, `psi` satisfies every clause of (b).

## Part 2

- **Root ⇒ (C) and (F).** Let `A` be finitely generated with solvable word problem.
  The root gives a finitely presented simple `S ≥ A`. By
  `fp-simple-algebras-have-solvable-word-problem`, `S` has solvable word problem,
  which proves (C). (F) is the root restricted to finitely presented inputs.
- **(C) and (F) ⇒ root.** (C) gives a finitely presented `B ≥ A` with solvable word
  problem, and (F) gives a finitely presented simple `S ≥ B`. So `A ≤ S`.
