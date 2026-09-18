---
rg: 2
id: fp-central-simple-host-with-nonzero-leavitt-k1
kind: claim
title: A finitely presented central simple crossed product of the virtually free group F_2 ⋊ Z/2 on ∂F_2 over F_2 contains F_2[F_2 ⋊ Z/2] and has K_1 of its Leavitt tensor nonzero
distinct_from:
  free-action-leavitt-tensor-hosts-have-trivial-k1-k2: that is the open vanishing statement for free actions, whose necessity example is a trivial Z/2 action; this is an effective, minimal, topologically free action with finitely presented central simple crossed product where K_1 of the Leavitt tensor is still nonzero.
  free-minimal-cantor-crossed-products-are-central-simple: that proves central simplicity for minimal topologically free actions; this applies it to one explicit action and shows the K-condition fails there.
  boundary-crossed-product-is-a-leavitt-path-algebra: that identifies LC(∂F_d) ⋊ F_d with a Leavitt path algebra; this uses it to get finite presentation of a Z/2-extension of it.
  leavitt-tensor-k1-sees-traces-of-nilpotent-matrices: that shows K_1(k[G] ⊗ L) != 0 for group algebras with p-torsion; this shows the same for a central simple host, where the group algebra's augmentation trace is unavailable.
---

**ESTABLISHED (elementary, from established claims; unreviewed).** Route:
`fp-central-simple-host-with-nonzero-leavitt-k1-proof`.

Let `N = F_2 = <c_1, c_2>` and let `α ∈ Aut(N)` be the involution `c_1 ↦ c_1`,
`c_2 ↦ c_2^(-1)`. Put `Γ = N ⋊ <σ>`, with `σ n σ = α(n)` and `σ^2 = e`. Then `Γ`
acts on `∂N`, the space of infinite reduced words, by

- `n · ξ = red(n ξ)` for `n ∈ N`;
- `σ · ξ = α(ξ)`, where `α` acts letter by letter.

Let `B = LC(∂N, F_2) ⋊ Γ` and `L = L_(F_2)(1,2)`.

**Theorem.**
1. `B` is finitely presented as an `F_2`-algebra.
2. The action is minimal and topologically free. Hence `B` is simple and
   `Z(B) = F_2`.
3. `γ ↦ u_γ` embeds `F_2[Γ]` unitally in `B`.
4. `(1 + u_σ)^2 = 0`, and `[1 + (1 + u_σ) ⊗ e_1] ≠ 0` in `K_1(B ⊗ L)`.

`Γ` is virtually free, hence hyperbolic, and satisfies the Farrell–Jones
conjecture (Bartels–Lück–Reich). This is context only and is not used in the
proof.

**What changes.** The host route in
`decidable-group-algebras-have-fp-central-simple-hosts` needs a finitely
presented central simple `B` with `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`. This example
shows that the K-condition is independent of all of the following together:

- finite presentation;
- central simplicity;
- containing the group algebra;
- a hyperbolic, Farrell–Jones acting group;
- a minimal, effective, topologically free action on a Cantor set.

So the K-condition must be arranged separately. For crossed products, the
obstruction is `crossed-product-fixed-point-traces-detect-leavitt-k1`: a
`p`-element whose fixed-point set carries a centralizer-invariant functional
that is nonzero on `1`. Here that is `σ`, which fixes `c_1^∞`.
