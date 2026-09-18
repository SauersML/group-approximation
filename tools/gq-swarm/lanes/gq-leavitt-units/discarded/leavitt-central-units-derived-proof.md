---
rg: 2
id: leavitt-central-units-derived-proof
kind: route
title: V-conjugate cone scalars have one class c modulo [P,P], and the codes {1,2} and {1,21,22} give c^2 = c^3; then the Schur multiplier of a finitely presented perfect group bounds the centre
target: leavitt-central-units-lie-in-derived-normal-subgroups
requires:
  - thompson-v-finitely-presented-infinite-simple
---

Notation as in the claim. For a finite word `a` over `{1,2}` write
`s_a = s_(a_1) ... s_(a_k)`, `t_a = t_(a_k) ... t_(a_1)` and `p_a = s_a t_a`. Then
`t_a s_a = 1`, and `p_a` is idempotent. For a complete prefix code `C` the `p_a`,
`a ∈ C`, are orthogonal and sum to `1`.

**Step 0 (V is a faithful copy).** For complete prefix codes `(α_i)`, `(β_i)` of equal
size, `g = Σ s_(β_i) t_(α_i)` is a unit with inverse `Σ s_(α_i) t_(β_i)`, and these units
form a homomorphic image of Thompson's `V`. The swap `w = s_1 t_2 + s_2 t_1` is nontrivial:
`t_1 w s_2 = 1`, whereas `t_1 s_2 = 0`, and `1 ≠ 0` because `R ≠ 0`. `V` is simple
(`thompson-v-finitely-presented-infinite-simple`), so the image is a faithful copy.

**Step 1 (cone scalars).** For `λ ∈ Z_R` and a nonempty word `a`, put
`e_a(λ) = λ p_a + (1 - p_a)`. It is a unit with inverse `e_a(λ^(-1))`, since `λ` is
central. For a complete prefix code `C`, the `e_a(λ)`, `a ∈ C`, commute and
```text
∏_(a∈C) e_a(λ) = λ Σ_(a∈C) p_a = λ.                                         (1)
```

**Step 2 (all cone scalars are V-conjugate).** Let `a, b` be nonempty words. Choose
complete prefix codes `(α_i)` containing `α_1 = a` and `(β_i)` containing `β_1 = b` of the
same size. Every nonempty word lies in a complete prefix code of size `≥ 2`, and splitting
a word other than `a`, respectively `b`, raises the size by one. For
`g = Σ s_(β_i) t_(α_i) ∈ V`, prefix-code orthogonality gives `g s_a = s_b` and
`t_a g^(-1) = t_b`. So `g p_a g^(-1) = p_b`, and since `λ` is central,
`g e_a(λ) g^(-1) = e_b(λ)`.

**Step 3 (part 1).** Let `P ⊴ U` with `V ≤ P`, and put `K = [P, P]`.
- `K` is characteristic in `P`, so `K ⊴ U`.
- `V` is perfect and `V ≤ P`, so `V = [V, V] ≤ K`.
- For `x ∈ K` and `u ∈ U`, `x u x^(-1) u^(-1) = x · (u x^(-1) u^(-1)) ∈ K`. So conjugation
  by elements of `K`, in particular of `V`, fixes every coset `uK`.

By Step 2, all `e_a(λ)` with `a` nonempty lie in one coset `c ∈ U/K`. By (1) for the
codes `{1, 2}` and `{1, 21, 22}`, where `s_(21) t_(21) = s_2 s_1 t_1 t_2`,
```text
λK = e_1(λ) e_2(λ) K = c^2,      λK = e_1(λ) e_21(λ) e_22(λ) K = c^3.
```
Hence `c = 1` in `U/K`, so `e_1(λ), e_2(λ) ∈ K` and `λ = e_1(λ) e_2(λ) ∈ K = [P, P]`.
With `P = [U,U]`, which contains `V = [V,V]`, this gives `Z_R ≤ [[U,U],[U,U]]`.

**Step 4 (Schur lemma).** *If `Q` is a perfect group, `A ≤ Z(Q)`, and `Q/A` is finitely
presented, then `A` is finitely generated.*
- `S = Q/A` is perfect, so it has a universal central extension `Ŝ -> S`, whose kernel is
  `H_2(S; Z)` (Milnor, *Introduction to algebraic K-theory*, §5).
- The induced map `Ŝ -> Q` over `S` is onto. Its image `H` satisfies `HA = Q`, so
  `Q = [Q,Q] = [HA, HA] = [H, H] ≤ H`.
- So `A` is the image of `H_2(S; Z)`.
- For `S = F/N`, with `F` free of finite rank and `N` the normal closure of `r_1..r_k`,
  Hopf's formula gives `H_2(S; Z) = (N ∩ [F,F])/[F,N] ≤ N/[F,N]`. The latter is generated
  by the images of `r_1..r_k`, because conjugates of `r_i` agree modulo `[F,N]`. So `A` is
  finitely generated.

**Step 5 (part 2).** Suppose `P/C` is perfect and finitely presented, with `C ≤ Z(P)` and
`Z_R ≤ C`.
- Perfectness gives `P = [P,P] C`. With `C` central,
  `[P,P] = [[P,P]C, [P,P]C] = [[P,P],[P,P]]`, so `P' = [P,P]` is perfect.
- `P'/(P' ∩ C) ≅ P'C/C = P/C` is finitely presented, and `P' ∩ C` is central in `P'`. By
  Step 4, `P' ∩ C` is finitely generated.
- By Step 3, `Z_R ≤ P'`, so `Z_R ≤ P' ∩ C`. A subgroup of a finitely generated abelian
  group is finitely generated, so `Z_R` is finitely generated. This contradicts the
  hypothesis.

A simple group is perfect unless it is cyclic of prime order. If `P/Z(P)` were cyclic,
`P` would be abelian and `P/Z(P)` trivial. So `P/Z(P)` is never a finitely presented
simple group.

QED
