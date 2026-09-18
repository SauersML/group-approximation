---
rg: 2
id: fox-rational-section-fails-class-two-virtually
kind: claim
title: For n at least four the Fox rational section of the abelianized Aut/Out extension lifts to class two over no finite-index subgroup, so a virtual section of Aut(F_n) to Out(F_n) forces nonzero H^1 of that subgroup with coefficients in H_Q
distinct_from:
  aut-out-free-nilpotent-tower-virtually-splits: that is the OPEN claim that every nilpotent level virtually splits, allowing twists; this shows the one canonical untwisted section fails at class two on every finite-index subgroup, and turns the twist freedom into a twisted H^1 condition.
  abelian-subgroups-of-out-free-virtually-lift-to-aut: that shows abelian subgroups virtually lift, so twisted sections pass every commuting-pair test; this shows the untwisted canonical section fails one such test.
---

**ESTABLISHED** (lane proof below, elementary; not reviewed; no novelty claimed).

Notation: `H = H_1(F_n)`, `N = F_n/γ_3`, `N_Q` its Mal'cev completion,
`E_1^Q`, `E_2^Q` the rationalized extensions of `Out(F_n)` by `H_Q` and `N_Q`.
Over `Q`, `k = h/(n − 1)` is a crossed homomorphism on all of `Aut(F_n)` with
`k(ι_g) = [g]`, so its zero set gives a section `σ` of `E_1^Q → Out(F_n)`: the
**Fox section**, `σ([φ]) = φ ι_u` with `[u] = −φ_*^{-1}k(φ)`.

**Theorem.** Let `n ≥ 4`.
1. For every finite-index `Γ' ≤ Out(F_n)`, `σ|_{Γ'}` does not lift to `E_2^Q`.
2. **Corollary.** If `Aut(F_n) → Out(F_n)`, or even `E_2 → Out(F_n)`, has a
   section `s` over a finite-index `Γ'`, then `H¹(Γ'; H_Q) ≠ 0`. More precisely,
   the crossed homomorphism `z` with `s = σ·z` in `E_1^Q` restricts to a nonzero
   homomorphism on `⟨ᾱ^m, β̄^m⟩` below.
3. For `n ≥ 7` there is `H¹(Out(F_n); H_Q) = 0` (Randal-Williams, see Attempt 2 of the
   tower node). So `E_2^Q → Out(F_n)` has no section, and the canonical class
   `o_Q ∈ H²(Out(F_n); Λ²H_Q)` is nonzero. For `n ≥ 11` it spans that `Q`.

So item (a) of Attempt 2 of `aut-out-free-nilpotent-tower-virtually-splits` is
settled: `o_Q ≠ 0`. Item (b) becomes the question whether
`H¹(Γ'; H_Q) = 0` for all finite-index `Γ' ≤ Out(F_n)`. A yes would show that
`Aut(F_n) → Out(F_n)` never virtually splits, for every `n ≥ 4`.

## Proof

1. **The pair.** `α = K_12: x_1 ↦ x_2x_1x_2^{-1}` and `β = K_34: x_3 ↦ x_4x_3x_4^{-1}`,
   with all other generators fixed. Both lie in `IA_n` and commute in `Aut(F_n)`.
2. **Their Fox values.** For `α`, the abelianized Jacobian is the identity except
   row 1, which is `(t_2, 1 − t_1, 0, …)`. Its determinant is `t_2`, so
   `h(α) = e_2` and `k(α) = s e_2` with `s = 1/(n − 1)`. Likewise `k(β) = s e_4`.
   Hence `σ(ᾱ^m) = α^m ι_{u^m}` and `σ(β̄^m) = β^m ι_{v^m}`, with
   `u = x_2^{-s}` and `v = x_4^{-s}` in `N_Q`.
3. **Everything commutes except the inner parts.** `α` fixes `x_2, x_4`, and `β`
   fixes `x_2, x_4`. So `α, β, ι_u, ι_v` pairwise commute, except `ι_u` with `ι_v`,
   and `(αι_u)^m = α^m ι_{u^m}`. The commutator of the two σ-values is
   `ι_{[u^m, v^m]}`, and `[u^m, v^m] ≡ m²s²·e_2∧e_4 ≠ 0` in `Λ²H_Q = γ_2/γ_3 ⊗ Q`.
4. **No lift commutes.** Any two lifts to `E_2^Q` differ from these by `ι_y` with
   `y ∈ Λ²H_Q`, central in `N_Q` and fixed by `IA_n`, so the commutator is
   unchanged. `ᾱ^m` and `β̄^m` commute in `Out(F_n)`, and a finite-index `Γ'`
   contains them for some `m ≥ 1`. So no homomorphic lift exists on `Γ'`.
5. **Corollary.**
   - `s` induces a section of `E_1^Q` over `Γ'`, which equals `σ·z` for some
     `z ∈ Z¹(Γ'; H_Q)`.
   - If `[z] = 0`, then `σ·z` is `σ` conjugated by some `h ∈ H_Q`. Conjugating
     `s` by a lift of `h` in `N_Q` then lifts `σ|_{Γ'}` to `E_2^Q`, contradicting
     item 4.
   - The same argument on `⟨ᾱ^m, β̄^m⟩` shows `z` is nonzero there. The
     `IA_n`-action is trivial there, so `H¹ = Hom`.
6. **Item 3.** By `H¹ = 0`, every rational section of `E_1^Q` over `Out(F_n)` is
   conjugate to `σ`, and item 4 applies with `Γ' = Out(F_n)`.

**Scope.** Nothing here decides virtual splitting: twists by nonzero classes of
`H¹(Γ'; H_Q)` are not controlled. `n = 3` is not covered, since the pair needs four
generators. Pairs in `IA_3` checked by hand (`K_12` with `K_32`) give zero.
