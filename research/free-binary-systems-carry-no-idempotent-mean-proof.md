---
rg: 2
id: free-binary-systems-carry-no-idempotent-mean-proof
kind: route
title: Moore's self-referential set Z has no consistent measure under an idempotent mean
target: free-binary-systems-carry-no-idempotent-mean
requires: []
artifacts:
  - experiments/free-magma-idempotent-2026-09-17/check_moore_z_set.py
---

This is a complete direct proof. It follows Section 2 of J. T. Moore, arXiv:1807.05469v1, with every step re-checked
and two small points repaired: the paper writes `r := μ(E)` for `r := μ(Z)`, and it uses without comment that the
chain `T_p` decreases.

**Setup.** `(S,*)` is free on `I ≠ ∅`. So `*` is an injection `S × S → S ∖ I`, and every `s ∉ I` is `a*b` for a
unique pair. Let `#: S → {1,2,…}` count generator occurrences, so `#(a*b) = #a + #b` and `#a, #b < #(a*b)`. Put
`S_n = {s : #s = n}`. Then `S_1 = I`, and `S_n = ⋃_{i+j=n, i,j≥1} S_i*S_j` for `n ≥ 2`. For `A, B ⊆ S` write
`A*B = {a*b : a ∈ A, b ∈ B}`.

**Definition of `Z` and `T_p`.** Define, by simultaneous recursion on `#s`:
- `T_0 = S`;
- `s ∈ T_{p+1}` iff `s = c*d` with `c ∉ Z` and `d ∈ T_p`;
- `s ∈ Z` iff `s = a*b` with `b ∈ T_{#a}`.

Membership of `s` refers only to elements of smaller `#`, so this is a valid recursion. So
`T_{p+1} = (S∖Z)*T_p` and `Z = ⋃_k S_k*T_k`.

**Lemma 1 (monotone).** `T_{p+1} ⊆ T_p` for all `p`.
*Proof.* `T_1 ⊆ S = T_0`. If `T_p ⊆ T_{p−1}`, then `T_{p+1} = (S∖Z)*T_p ⊆ (S∖Z)*T_{p−1} = T_p`. ∎

**Lemma 2 (sections).** For every `s ∈ S`, `{t : s*t ∈ Z} = T_{#s}`.
*Proof.* By injectivity, `s*t = a*b` forces `a = s` and `b = t`. So `s*t ∈ Z` iff `t ∈ T_{#s}`. ∎

**Fact A (rectangles).** For means `μ, ν` and `A, B ⊆ S`, `μ*ν(A*B) = μ(A)ν(B)`.
*Proof.* By Lemma 2's injectivity argument, for `s ∈ A` the section `{t : s*t ∈ A*B}` is `B`, and for `s ∉ A` it is
empty. So the inner integral is the function `ν(B)·χ_A(s)`, and its `μ`-integral is `μ(A)ν(B)`. ∎

**Fact B (constant sections).** If `ν({t : s*t ∈ X}) = c` for every `s`, then `μ*ν(X) = c`, because the inner
integral is the constant function `c`.

**Proof of the claim.** Suppose `μ*μ = μ`, and put `r = μ(Z)`.
1. `μ(S*S) = μ*μ(S*S) = μ(S)² = 1` by Fact A. Freeness gives `I = S∖S*S`, so `μ(S_1) = μ(I) = 0`.
2. By strong induction, `μ(S_n) = 0` for all `n ≥ 1`. For `n ≥ 2`, `μ(S_n) ≤ Σ_{i+j=n} μ*μ(S_i*S_j)`, which by
   Fact A is `Σ_{i+j=n} μ(S_i)μ(S_j) = 0`. The sum is finite, so finite subadditivity suffices.
3. `μ(T_p) = (1−r)^p`, by induction: `μ(T_{p+1}) = μ*μ((S∖Z)*T_p) = (1−r)μ(T_p)` by Fact A.
4. *Case `r > 0`.* Choose `n` with `(1−r)^n < r`. For `k ≥ n`, Lemma 1 gives `S_k*T_k ⊆ S*T_n`. So
   `Z ⊆ (⋃_{k<n} S_k)*S ∪ S*T_n`. By idempotence and Fact A,
   `r = μ(Z) ≤ μ(⋃_{k<n}S_k)·μ(S) + μ(S)·μ(T_n) = 0 + (1−r)^n < r`.
   This is a contradiction.
5. *Case `r = 0`.* By step 3, `μ(T_p) = 1` for every `p`. By Lemma 2 each section `{t : s*t ∈ Z}` has
   `μ`-measure 1. By Fact B, `μ(Z) = μ*μ(Z) = 1 ≠ 0 = r`. This is a contradiction. ∎

**What the proof uses.** Only injectivity of `*`, the additive grading `#`, and finite additivity. It never uses a
single generator, countability, or any topology on the space of means. The weak* discontinuity of `μ ↦ μ*μ` is
why no fixed-point theorem applies: the finite-quotient pushforwards all have fixed points by Brouwer, as recorded
on `free-magma-carries-an-idempotent-finitely-additive-measure`.

**Machine check.** `python3 experiments/free-magma-idempotent-2026-09-17/check_moore_z_set.py 11` enumerates all
trees with at most 11 leaves on one generator (16796 at size 11). It checks Lemma 1 for all `p ≤ 11`, and Lemma 2
for all pairs with total size at most 11. It exits 0 with no failures. Among size-`n` trees the density of `Z` falls
slowly (0.2895 at `n = 11`). So `Z` is a genuinely intermediate set, not a finite-level artefact.
