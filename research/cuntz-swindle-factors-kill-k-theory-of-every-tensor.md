---
rg: 2
id: cuntz-swindle-factors-kill-k-theory-of-every-tensor
kind: claim
title: An algebra with a Cuntz pair and an endomorphism satisfying sigma = id ⊞ sigma kills the K-theory of its tensor product with every algebra, has no nonzero trace, and L_2 is not such an algebra
distinct_from:
  leavitt-tensor-kills-k1-of-coefficient-matrices: that is the corner swindle phi(r) = e r e* + f r f*, which fixes B ⊗ 1 and so kills only the image of K_1(B); this uses an endomorphism sigma with sigma = id ⊞ sigma on the whole algebra, which kills all of K_q(D ⊗ A) for every D and every q.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that kills K_*(B ⊗ L_2) only for regular supercoherent B; this kills K_*(D ⊗ A) for arbitrary D, at the price of a factor A carrying a swindle endomorphism, which L_2 does not carry.
  leavitt-tensor-k-theory-is-pure-twisted-nil: that shows the obstruction over L_2 is two twisted Nil terms, nonzero for some coefficients; this gives a tensor factor for which the Nil terms, and everything else, vanish for all coefficients.
  leavitt-tensor-k1-sees-traces-of-nilpotent-matrices: that detects nonzero K_1(k[ε] ⊗ L_2); this uses that as the reason L_2 has no swindle endomorphism.
---

**ESTABLISHED.** Route: `cuntz-swindle-factors-kill-k-theory-of-every-tensor-proof`.

Let `k` be a field and `A` a unital `k`-algebra. A **Cuntz swindle structure** on `A` is:
- elements `s_1, s_2, s_1^*, s_2^*` of `A` with `s_i^* s_j = δ_ij` and `s_1 s_1^* + s_2 s_2^* = 1`;
- a unital `k`-algebra endomorphism `σ : A -> A` with

  ```text
  σ(a) = s_1 a s_1^* + s_2 σ(a) s_2^*      for every a ∈ A.        (S)
  ```

For unital endomorphisms `α, β` write `α ⊞ β` for the map `a -> s_1 α(a) s_1^* + s_2 β(a) s_2^*`. Then (S)
says `σ = id ⊞ σ`.

1. **(All tensors are K-trivial.)** If `A` carries a Cuntz swindle structure, then
   `K_q(D ⊗_k A) = 0` for every unital `k`-algebra `D` and every `q ∈ Z`.
2. **(No traces.)** If `A` carries a Cuntz swindle structure, then every additive map `τ : A -> M` to
   an abelian group with `τ(xy) = τ(yx)` is zero. So `A = [A, A]` and `HH_0(A) = 0`.
3. **(L_2 is not such a factor.)** `L_k(1,2)` carries no Cuntz swindle structure, for any choice of
   Cuntz pair in it. By item 1, one would force `K_1(k[ε] ⊗ L_k(1,2)) = 0`, contradicting
   `leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`, Corollary 3.
4. **(Two easy forms are impossible.)** In a nonzero `A` with a Cuntz swindle structure:
   - `σ` is not conjugation by a unit of `A`;
   - `σ ∘ σ ≠ σ`.

   So a swindle endomorphism is never inner, and never idempotent.

## Why it matters

Every Leavitt-tensor Boone–Higman route (`boone-higman-via-central-simple-leavitt-tensor-host`,
`boone-higman-via-essential-shell-germ-algebras`, the Cantor crossed product lanes) carries a
per-input K-gate: `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`, or finite normal generation of an unstable
Steinberg kernel. By item 1, one fixed finitely presented central simple algebra `A` with a
Cuntz swindle structure would discharge that gate for every input at once. The input `B` is
replaced by `B ⊗ A`, and `(B ⊗ A) ⊗ L ≅ (B ⊗ L) ⊗ A`. This is the route
`fp-central-simple-hosts-via-cuntz-swindle-factor`, and the open existence statement is
`fp-central-simple-cuntz-swindle-algebra-exists`.

DERIVATION
cuntz-swindle-factors-kill-k-theory-of-every-tensor-proof
