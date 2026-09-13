---
rg: 2
id: polynomially-representable-envelopes-via-leavitt-tensors
kind: route
title: Tensor powers of the central simple Leavitt algebra host free and polynomial algebras
requires:
  - leavitt-nekrashevych-completion-simplicity-criterion
target: polynomially-representable-algebras-have-fp-simple-envelopes
---

Notation as in the claim.

## 1. L_2 is finitely presented, simple and central

`L_2` has 4 generators and 5 relators. By part 4 of
`leavitt-nekrashevych-completion-simplicity-criterion`, it is simple with center `K`.

## 2. Tensor lemma

**Lemma.** If `A` is a simple `K`-algebra and `B` is a simple `K`-algebra with
center `K`, then `A ⊗_K B` is simple.

*Proof.*

- *Setup.* Let `I ≠ 0` be an ideal. Pick `x = sum_{i=1}^r a_i ⊗ b_i in I \ {0}`
  with `r` minimal. Then `a_1..a_r` and `b_1..b_r` are each linearly independent.
- *Normalize the first coefficient.* Since `B` is simple and `b_1 ≠ 0`, there are
  `u_l, v_l in B` with `sum_l u_l b_1 v_l = 1`. Then
  `x' = sum_l (1 ⊗ u_l) x (1 ⊗ v_l) = a_1 ⊗ 1 + sum_{i >= 2} a_i ⊗ b'_i in I`,
  and `x' ≠ 0` because the `a_i` are independent.
- *The remaining coefficients are central.* For `b in B`,
  `(1 ⊗ b) x' - x' (1 ⊗ b) = sum_{i >= 2} a_i ⊗ [b, b'_i] in I` has fewer than `r`
  terms, so it is `0`. By independence of the `a_i`, every `b'_i` is central, so
  `b'_i = λ_i in K`.
- *Conclusion.* `x' = a ⊗ 1` with `a = a_1 + sum λ_i a_i ≠ 0`. Since `A` is simple,
  `1 ⊗ 1 in (A a A) ⊗ 1 ⊆ I`, so `I = A ⊗ B`. ∎

**Consequences.**

- *Tensor powers.* By induction, taking `B = L_2` at each step, every tensor power
  `L_2^{⊗ j}` is simple.
- *Matrix algebras.* `M_n(K)` is simple with center `K`, so
  `M_n(S) = S ⊗ M_n(K)` is simple whenever `S` is.
- *Finite presentation.* A tensor product of finitely presented algebras is
  finitely presented: take the union of generators and relators, plus the
  commutation relators between the two generating sets. `M_n(K)` is finitely
  presented. This proves part 1.

## 3. Embeddings

**Words in `s_1, s_2` are linearly independent in `L_2`.** A word `s_alpha` lies in
degree `|alpha|`. At level 0 it has a single nonzero coefficient, `1` at index
`(alpha, ∅)`. By part 1 of `leavitt-nekrashevych-completion-simplicity-criterion`,
distinct words of equal length are independent, and words of different lengths
lie in different graded pieces.

**The embeddings.**

- *Free algebra.* Send `x_i |-> s_1^{i-1} s_2`. The set
  `{ s_2, s_1 s_2, s_1^2 s_2, ... }` is a prefix code, so distinct monomials in the
  `x_i` map to distinct words `s_alpha`. So `K<x_1..x_m> -> L_2` is injective.
- *Polynomial algebra.* Send `t |-> s_1`. Distinct powers are distinct words, so
  `K[t] -> L_2` is injective.
- *Assembling.* Tensor products of injective linear maps over a field are
  injective, so `K<x_1..x_m> ⊗ K[t_1] ⊗ ... ⊗ K[t_k] -> L_2^{⊗(k+1)}` is injective.
  Applying `M_n(-)` preserves injectivity. This proves part 2.

Part 3 follows, since restricting an embedding to a subalgebra is still an embedding.

## 4. Word problems

The covered inputs share one recursive time bound. Take a word of length `l` in
the generators of a subalgebra of `P_{m,k,n}`, with generators given as matrices
over `K<x> ⊗ K[t]`. Multiply out to an `n × n` matrix of polynomials, with at most
`C^l` monomials for a constant `C` depending on the generating set, and test
whether it is zero. That takes time exponential in `l`, uniformly over the class.
This is consistent with `no-fp-simple-algebra-hosts-every-decidable-algebra`, and it
is why this class cannot clear that complexity benchmark.
