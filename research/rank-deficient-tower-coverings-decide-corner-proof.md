---
rg: 2
id: rank-deficient-tower-coverings-decide-corner-proof
kind: route
title: A rank-deficient tower covering splits the algebra into too few tower ideals, which the one-value gap forbids unless every state sees the corner as the unit
target: rank-deficient-tower-coverings-decide-binary-cyclic-corner
requires:
  - binary-cyclic-corner-full-iff-complement-corner-has-no-state
artifacts:
  - research/artifacts/gk3-binary-fullness-2026-09-14.md
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

Complete direct proof (artifact Section 2). Notation of `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md`
([CS]): `u = [A]`, `p = [eA]`, `v = [fA]` with `f = 1 - e`, `p_k = [E_k A]`, `d_k = [(E_k - E_(k+1)) A]`,
`T = fAf`, `ψ'(x) = f D(x)`, `ι_T` the corner inclusion.

1. **1 => 2.** Take `k = 1`, `r = 1`, `a_1 = c`, `b_1 = b`.
2. **2 => a split.** Put the row `R = (a_1 E_k, ..., a_r E_k)` and the column `C = (E_k b_1, ..., E_k b_r)`.
   Since `E_k² = E_k`, `R C = Σ_j a_j E_k b_j = 1`. So `y -> C y` is a split injection `A -> (E_k A)^r` with
   retraction `m -> R m`, and `u <= r p_k` in `V(A)`.
3. **A positive corner value forces the profile.** Let `s` be a state on `(K_0(A), u)` with `x = s(v) > 0`.
   - `K_0(ι_T)` is positive and sends `[T]` to `v`, so `s_T = x^(-1) · s ∘ K_0(ι_T)` is a state on `(K_0(T), [T])`.
   - Step 4 => 5 of [CS] Theorem B: `ψ'` is unital, `ψ'(f) = f_(K_3) + f_(K_4)`, and `f_(K_2)`, `f_(K_3)`, `f_(K_4)`
     are orthogonal, pairwise equivalent in `T` and sum to `f`. So `s' = s_T ∘ K_0(ψ')` is a state on `(K_0(A), u)`
     with `s'(v) = 2/3`.
4. **The profile values.** [CS] Lemma 1.2(b),(c) give `v = 3^k d_k` and `p = p_(k+1) + ((3^k - 1)/2) d_k`. With
   `s'(v) = 2/3`: `s'(p) = 1/3`, `s'(d_k) = 2 · 3^(-(k+1))`, and `s'(p_(k+1)) = 1/3 - (3^k - 1)/3^(k+1) = 3^(-(k+1))`.
   Together with `p_1 = p`, this gives `s'(p_k) = 3^(-k)` for every `k >= 1`.
5. **Contradiction.** Step 2 gives `1 = s'(u) <= r · s'(p_k) = r / 3^k < 1`. So no state has `s(v) > 0`: every
   state gives `[e]` the value `1`. That is statement 4 of [CS] Theorem B, and Theorem B (4 => 1) gives `c e b = 1`.
6. **Coset form.** For `x` in `Γ`, `x E_k b = (x E_k x^(-1))(x b)`, and `x E_k x^(-1) = Σ_(h in K) [h]` with
   `K = x C_3^k x^(-1)`. Since `|K| = 3^k` is odd, `a` lies in `E^(K) A` iff `[h] a = a` for all `h` in `K`: one
   direction because `[h] E^(K) = E^(K)`, the other because then `E^(K) a = 3^k a = a`. As functions on `Γ` these
   are the finitely supported functions constant on the sets `K w`.

Steps 3–4 are Theorem 1.1(b),(d) of `research/artifacts/brin-thompson-2v-obstruction-state-profile-2026-09-12.md`,
restated here for a general host. The only outside input is inside [CS] Theorem B (the state criterion for a unital
ring, used in 5 => 6 there).
