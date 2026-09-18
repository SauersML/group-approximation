---
rg: 2
id: leavitt-doubling-is-stably-conjugate-to-stabilization-proof
kind: route
title: The Leavitt pair gives mutually inverse rectangular matrices T and S; conjugating by diag(T, S) turns stabilization into doubling, and perfectness removes the central ambiguity
target: leavitt-doubling-is-stably-conjugate-to-stabilization
requires:
  - leavitt-resolvent-ring-is-fp-simple-of-char-zero
---

**Inputs.** Textbook, not re-read:
- `St_N(R)` is perfect for `N >= 3`;
- `GL(R)` acts on `St(R)` lifting conjugation on `E(R)`, and it acts trivially on `K_2(R)`;
- `K_2(R)` is central in `St(R)` (Weibel, *The K-book*, III Theorem 5.2.1).

**Item 1.**
- For `I != J`, the factors `x_((I,a),(J,b))` commute pairwise, since their index pairs share no inner index. So
  `x_IJ(A)` is well defined and additive in `A`.
- *The commutator relation.* For distinct `I, J, K`:
  - the only nontrivial commutators among the factors of `x_IJ(A)` and `x_JK(B)` are
    `[x_((I,a),(J,b))(α), x_((J,b),(K,d))(β')] = x_((I,a),(K,d))(αβ')`;
  - these commute with every factor involved.

  Hence `[x_IJ(A), x_JK(B)] = Π_(a,d) x_((I,a),(K,d))(Σ_b A_ab B_bd) = x_IK(AB)`.
- For `J != K` and `I != L`, the factors of `x_IJ(A)` and `x_KL(B)` commute.
- So `β` respects the Steinberg relations. It lifts the block inclusion. ∎

**Item 2.**
- *The inverse matrices.* `ST = diag(s_1 t_1 + s_2 t_2) = I_N`, and `TS = diag((t_a s_b)_(a,b)) = diag(I_2) = I_(2N)`.
- *The conjugation.* `D(g)` has `(I,J)` block `t g_IJ s`, so `D(g) = T g S`. The block product gives
  `U (g ⊕ I_(2N)) U^(-1) = (T g S) ⊕ (S T) = D(g) ⊕ I_N`, with `U^(-1) = [[S, 0],[0, T]]`.
- *The stable identity.*
  - `stab ∘ D` and `c_U ∘ stab` are homomorphisms `St_N(R) -> St(R)` with the same image in `E(R)`.
  - So `y ↦ (stab D y)(c_U stab y)^(-1)` is a homomorphism into the central, abelian `K_2(R)`.
  - It vanishes because `St_N(R)` is perfect. ∎

**Item 3.**
- (a) For `x ∈ K_2(N,R)`, item 2 gives `ι_(2N)(D x) = c_U(ι_N x) = ι_N x`, because `GL(R)` acts trivially on
  `K_2(R)`.
- (b) If `ι_N x = 1`, then `ι_(2N)(D x) = 1`, so `D x = 1`, so `x = 1`. The last step uses injectivity of `β` and
  bijectivity of `St_N(Ψ^(-1))` on `K_2`.
- (c) Every `y ∈ K_2(2N,R)` is `D x` for a unique `x`, and `ι_(2N) y = ι_N x` by (a). ∎
