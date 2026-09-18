---
rg: 2
id: field-envelopes-pass-to-algebraic-closures
kind: claim
title: If a field embeds in a finitely presented simple ring then so does its algebraic closure, so every countable field of finite transcendence degree over Q does
distinct_from:
  char-zero-representable-rings-embed-in-fp-simple-rings: that covers finitely generated fields, through finite-dimensional regular representations; this covers infinite algebraic extensions such as the algebraic closure of Q, through an ultramatricial chain inside a Leavitt algebra.
  countable-char-zero-fields-embed-in-fp-simple-rings: that is the open statement for all countable fields of characteristic zero; this settles the ones of finite transcendence degree and reduces the rest to Q(t_1, t_2, ...).
  rational-function-fields-embed-in-fp-simple-rings: that provides the purely transcendental base fields Q(t_1..t_k); this passes to all their algebraic extensions.
---

**ESTABLISHED** through `field-envelopes-pass-to-algebraic-closures-proof` (lane proof; refereed PASS by `gq-referee-a` (proof gaps, `gq-referee-a-field-envelopes-pass-to-algebraic-closures.md`, 69a3cc64f) and `gq-referee-b` (`gq-referee-b-rational-function-fields-embed-in-fp-simple-rings.md`, d7414d7a4)). No priority is claimed.

**Statement.**
1. **Transfer.** Let `K` be a field of characteristic zero that embeds in a finitely
   presented simple ring `R`. Then the algebraic closure `K̄` embeds in the finitely
   presented simple ring `R ⊗_Q L_Q(1,2)`, unitally if `K ⊆ R` is unital. Hence so does every algebraic
   extension of `K`, together with all its matrix rings.
2. **Finite transcendence degree.** Every countable field of characteristic zero with
   finite transcendence degree `k` over `Q` embeds unitally in
   `R_k ⊗_Q L_Q(1,2)`, where `R_k` is the ring of
   `rational-function-fields-embed-in-fp-simple-rings`, with `R_0 = R_L`. Examples:
   - `Q̄`, which already lies in `R_L`, since `R_L ⊇ L_Q(1,2)`;
   - every algebraic extension of `Q`;
   - `Q̄(t)` and the algebraic closure of `Q(t_1..t_k)`.
3. **Consequence.** `GL_n(Q̄)` embeds in `R_L^x`. For a countable field `K` of
   characteristic zero and finite transcendence degree `k >= 1`, `GL_n(K)` embeds in
   `(R_k ⊗_Q L_Q(1,2))^x`. By `leavitt-scalar-commutators-block-fp-central-quotients`,
   such unit groups have no finitely presented quotient by a central subgroup containing
   `Q^x`.

**Mechanism.**
- A countable algebraic extension `E = ∪ E_i` of `K`, with `[E_i : K] = d_i`, embeds in the
  ultramatricial `K`-algebra `colim M_(d_i)(K)` by compatible regular representations.
- That algebra embeds unitally in `L_K(1,2)`, because `L_K(1,2) ≅ M_r(L_K(1,2))` for every
  `r >= 1`, and these isomorphisms can be composed compatibly along the chain.
- Finally `L_K(1,2) = K ⊗_Q L_Q(1,2) ⊆ R ⊗_Q L_Q(1,2)`.
