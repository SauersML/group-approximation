---
rg: 2
id: horner-resolvent-leavitt-tensor-k1-k2-vanish
kind: claim
title: For the Horner-resolvent algebra R_2 over F_2, the Leavitt tensor R_2 ⊗ L_(F_2)(1,2) has K_1 = K_2 = 0
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that gives K_*(L_2 ⊗ R) = 0 for regular supercoherent R; this asks it for one explicit R, the Horner-resolvent completion, which is not known to be regular supercoherent.
  leavitt-tensor-powers-have-trivial-k-theory: that is the same vanishing for tensor powers of L; this is for a Leavitt--Nekrashevych completion of a commutative regular ring with one non-flat reset letter.
  leavitt-resolvent-k-theory-is-shifted-rational-k-theory: that computes K_*(R_L) itself in characteristic zero, and it is nonzero; this asks for the K-theory of the Leavitt tensor in characteristic two, where the expected answer is zero.
---

**OPEN.** Let `R_2` be the algebra of `char-p-rational-function-field-in-fp-simple-algebra`
with `p = 2`, and `L = L_(F_2)(1,2)`. Then `K_1(R_2 ⊗ L) = K_2(R_2 ⊗ L) = 0`.

**Why it matters.** It is the only open input of `gl-n-f2t-bh-via-horner-resolvent-leavitt-tensor`,
which then puts every `GL_n(F_2(t))`, all `n` at once, in one finitely presented simple group
`(R_2 ⊗ L)^x`. Finite normal generation of `ker(St_n(R_2 ⊗ L) -> E_n(R_2 ⊗ L))` for one `n >= 4`
would also do, through `leavitt-tensor-elementary-host-criterion` applied to
`B = M_(n+1)(R_2)` and the perfect group `SL_(n+1)(F_2(t)) ⊇ GL_n(F_2(t))`.

**Sufficient conditions.**
1. `R_2` is regular supercoherent: then `K_*(L ⊗ R_2) = 0` by Ara--Cortiñas Proposition 6.2
   (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).
2. A Pimsner-type long exact sequence for `R_2 ⊗ L`, viewed as the Leavitt--Nekrashevych
   completion of `B ⊗ L` along `ψ ⊗ id` (the covariance `ℓ = Σ_x s_x ℓ t_x` makes the two
   presentations agree), with coefficients whose own `K`-theory vanishes. For the commutative
   base `B = S^(−1) F_2[t, P]`, which is regular noetherian, `K_*(B ⊗ L) = 0` by Proposition 6.2.

## Attempts
1. **The reset letter is not flat.** `σ_v : B -> B` (`P ↦ 1`) makes `B` a module over itself
   through `F_2[t,P] -> F_2[t]`, which is not flat. So the core `colim M_(d^n)(B)` along `ψ` is a
   colimit along non-flat maps, and regular coherence of the core does not follow from that of `B`.
   This is the same obstacle as for the characteristic-zero resolvent ring `R_L`, where
   `register-completion-pimsner-from-supercoherence` removes it by enlarging the coefficients with
   point indicators. That node covers one register over `Q` with letters
   `N ↦ N + a`, `N ↦ pN + r`, `N ↦ c`. Here there are two registers and the letter `t ↦ t^2`.
   Adapting it is the natural route.
2. **Expected answer.** In characteristic zero the Pimsner sequence gave
   `K_n(R_L) ≅ K_(n−1)(Q)`: the cokernel of `1 − [X]` comes from the reset letter. Tensoring with
   `L`, where `[1] = 2[1]`, should kill every such class, as `1 − 2 = −1` does for `L` itself.
   This is a heuristic, not a proof.
