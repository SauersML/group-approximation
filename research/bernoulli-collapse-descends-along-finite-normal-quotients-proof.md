---
rg: 2
id: bernoulli-collapse-descends-along-finite-normal-quotients-proof
kind: route
title: Identify generalized shifts over the quotient with co-induced shifts from the kernel, lift the quotient isomorphism, and absorb both sides into Bernoulli shifts
target: bernoulli-collapse-descends-along-finite-normal-quotients
requires:
  - coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - bernoulli-isomorphism-collapse-set-is-a-subgroup
  - bernoulli-collapse-is-null-or-eventually-total
artifacts:
  - research/artifacts/bernoulli-collapse-finite-kernel-descent-2026-09-17.md
---

"Section n" refers to the artifact. The prerequisites supply:
- Corollary D: `Coind(Y) × K^G ≅ M^G` when `|F| ≥ 2`, `H(Y) < ∞`, `0 < H(K) < ∞` and
  `H(M) = H(K) + H(Y)/|F|`, for `G` countably infinite (the first);
- well-definedness of `X_h`, so that finite bases can be chosen (the second);
- translation, which covers `n = 1`, and the definition of `D` (the third);
- `R(G) ⊆ [s, ∞)`, upward closed (item 3 of the fourth).

**Lemma 1.1 (Section 1).** A point of `Coind_N^Γ(L)` with trivial `N`-action is a function on `Γ` constant on the
cosets `tN`. These are the fibres of `Γ → Q`, since `N` is normal. So `Coind_N^Γ(L) = L^Q`, with `Γ` acting through
`Q`, and the transversal product measure is `λ^Q`.

**Theorem A (Section 2).**
- Take finite bases `L_a`, `L_b`, and a `Q`-isomorphism `π: L_a^Q → L_b^Q`. It is `Γ`-equivariant for the action
  through `Q`.
- Take `K` finite with `H(K) = c > 0`. Then `π × id` is a `Γ`-isomorphism `L_a^Q × K^Γ → L_b^Q × K^Γ`.
- By Lemma 1.1 and Corollary D with `F = N`, `Y = L_a` and `Y = L_b`, the two sides are `X_(c + a/n)` and
  `X_(c + b/n)` over `Γ`. `Γ` is infinite, as Corollary D requires.

**Corollary (Corollary A.1).**
- Item 1: apply Theorem A to a witness `h, h + d` of `d ∈ D(Q)`. Both levels are finite and positive.
- Item 2: Theorem A makes every `c + a/n` with `c > 0` non-rigid.
- Item 3: combine item 2 with `R(Γ) ⊆ [s(Γ), ∞)`.
- Item 4: the contrapositive of item 1.
