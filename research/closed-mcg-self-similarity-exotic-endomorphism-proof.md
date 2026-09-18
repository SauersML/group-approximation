---
rg: 2
id: closed-mcg-self-similarity-exotic-endomorphism-proof
kind: route
title: The level kernels of a self-similar action satisfy a section recursion, and Irmak rigidity plus a normal core in the extended mapping class group trap a finite-index subgroup in every level kernel
target: closed-mcg-self-similarity-needs-exotic-virtual-endomorphisms
requires:
  - closed-mcg-finite-index-injections-are-conjugations
---

Notation as in the target. Let `K_n ⊴ L` be the kernel of the action of `L` on words of
length at most `n`. Each `K_n` has finite index, and the action is faithful iff
`⋂_n K_n = 1`.

**Step 1 (recursion).** `K_1 ⊆ H_x` for every `x`, and for `n ≥ 1`

    K_{n+1} = K_1 ∩ ⋂_{x ∈ X} φ_x^{-1}(K_n).

This holds because `h ∈ L` fixes every word of length at most `n+1` iff two things
hold: `h` fixes every letter, and for every `x` the section `h|_x` fixes every word of
length at most `n`. The second condition uses `h(x w) = x h|_x(w)` for `h ∈ K_1`.

**Step 2 (rigidity).** Assume, for contradiction, that every `φ_x` is injective or has
finite image.
- If `φ_x` is injective: `H_x` has finite index in `Mod^±(S_g)`, and `φ_x` is an
  injection into `L ≤ Mod^±(S_g)`. So by `closed-mcg-finite-index-injections-are-conjugations`
  there is `t_x ∈ Mod^±(S_g)` with `φ_x(h) = t_x h t_x^{-1}` for all `h ∈ H_x`.
- If `φ_x` has finite image: `ker φ_x` has finite index in `H_x`.

**Step 3 (a normal subgroup of the extended group).** Put
`M_0 = K_1 ∩ ⋂ {ker φ_x : φ_x has finite image}`. It has finite index in `L`, so in
`Mod^±(S_g)`. Let `M` be its normal core in `Mod^±(S_g)`. Then `M` has finite index,
`M ⊴ Mod^±(S_g)`, and `M ⊆ M_0 ⊆ K_1`.

**Step 4 (induction).** We show `M ⊆ K_n` for every `n ≥ 1`. The case `n = 1` holds.
Suppose `M ⊆ K_n`, and let `h ∈ M`. Then `h ∈ K_1 ⊆ H_x` for every `x`, and:
- if `φ_x` has finite image, `φ_x(h) = 1 ∈ K_n`, since `M ⊆ ker φ_x`;
- if `φ_x` is injective, `φ_x(h) = t_x h t_x^{-1} ∈ t_x M t_x^{-1} = M ⊆ K_n`.

By Step 1, `h ∈ K_{n+1}`.

**Step 5.** So `M ⊆ ⋂_n K_n`. But `M` has finite index in the infinite group
`Mod^±(S_g)`, so `M ≠ 1`, and the action is not faithful. This contradicts the
hypothesis. □

**Remark.** Steps 1–4 do not use faithfulness. They show that if every section
homomorphism is injective or has finite image, then every self-similar action of `L` on a
finitely branching rooted tree factors through a finite quotient of `L`.
