---
rg: 2
id: outer-extension-word-problem-kernel-bound-proof
kind: route
title: Kill the centralizer, then decide triviality by the action on kernel generators after one exponential substitution
target: outer-extension-word-problem-is-kernel-bounded
requires: []
---

Notation as in the target.

**(OE1).** Let `c ∈ I` act trivially on `S` by conjugation. Its coset `cS`
maps to the trivial element of `Out(S)`, and `I/S → Out(S)` is injective, so
`c ∈ S`. Then `c` lies in `S` and centralizes it, so `c ∈ Z(S) = 1`.

**Data.** Let `X` be the finite generating set of `S` for which the word
problem is in `F(g)`, decided in time `C_S*g(C_S*n) + C_S*n + C_S`. Choose a
finite `Z ⊂ I` with `I = ⟨X ∪ Z⟩`, and put `Y = X ∪ Z`. Since `S ⊴ I`, for
each `y ∈ Y ∪ Y^(-1)` and each `x ∈ X ∪ X^(-1)` fix a word `u(y,x)` over
`X ∪ X^(-1)` with `y x y^(-1) = u(y,x)` in `S`. Let `L ≥ 2` bound the lengths
`|u(y,x)|`. This is finitely much data, depending on `I`.

**Algorithm.** Given a word `w = y_1 ⋯ y_l` over `Y ∪ Y^(-1)`:
1. For each `x ∈ X`, compute a word `v_x` over `X ∪ X^(-1)` representing
   `w x w^(-1)` in `S`. Start from the one-letter word `x`. For
   `k = l, l−1, …, 1`, replace every letter `x'` by `u(y_k, x')`. Each step
   multiplies the length by at most `L`, so `|v_x| ≤ L^l`. The total work is
   at most `A*l*L^l` for a constant `A` covering table lookups.
2. Decide whether `v_x x^(-1) = 1` in `S`, using the algorithm for `S`.
3. Answer `w = 1` iff all `|X|` tests succeed.

**Correctness.** By construction `w x w^(-1) = v_x` in `S`. So all tests
succeed iff conjugation by `w` fixes every generator of `S`, iff it is the
identity automorphism of `S`, iff `w = 1` in `I` by (OE1).

**Time.** Put `m = L^l + 1`. The running time is at most

```text
|X| * ( A*l*L^l + C_S*g(C_S*m) + C_S*m + C_S ).
```

For `l ≥ 1` we have `C_S*m ≤ 2*C_S*L^l ≤ 2^(c*l)` with
`c = ⌈log2(2*C_S) + log2(L)⌉`. So by monotonicity `g(C_S*m) ≤ g(2^(c*l))`.
Also `A*l*L^l ≤ A*2^(c'*l)` with `c' = 1 + ⌈log2(L)⌉`. With
`G(n) = g(2^n) + 2^n`, which is non-decreasing, each summand is at most a
constant times `G(C*l)` for `C = max(c, c')`. Hence for a large enough constant
`C_I` the time is at most `C_I*G(C_I*l) + C_I*l + C_I`, and the case `l = 0`
is absorbed in the constant. `∎`
