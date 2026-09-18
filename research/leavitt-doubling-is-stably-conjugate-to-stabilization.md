---
rg: 2
id: leavitt-doubling-is-stably-conjugate-to-stabilization
kind: claim
title: For a ring with a Leavitt pair, the Morita doubling St_N(R) ≅ St_N(M_2(R)) -> St_2N(R) is stably conjugate to stabilization, so injective stability at N follows from injective stability at 2N plus injectivity of the block map, and is equivalent to it when the block map is bijective on K_2
distinct_from:
  st-n-leavitt-resolvent-word-problem-reduces-to-k2: that reduces gate 1 to injective stability (i) of K_2(N,R_L) -> K_2(R_L); this tests the Morita-shift lever for (i) and shows what it does and does not give.
  k2-central-in-steinberg-groups-of-leavitt-resolvent-ring: that names the matrix-ring shift as a possible route to injective stability; this carries it out.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)** for items 1–3 through `leavitt-doubling-is-stably-conjugate-to-stabilization-proof`.
Lane proof (gq-k2-q), elementary, not independently reviewed. Item 4 is OPEN.

## Setting

- `R` is a unital ring with `s_1, s_2, t_1, t_2` such that `t_a s_b = δ_ab` and `s_1 t_1 + s_2 t_2 = 1`. For example
  `R = R_L`.
- `Ψ^(-1) : R -> M_2(R)`, `r ↦ (t_a r s_b)_(a,b)`, is a unital ring isomorphism.
- `N >= 3`.

## Statement

1. **The block map.** `β : St_N(M_2(R)) -> St_(2N)(R)`, `x_IJ(A) ↦ Π_(a,b) x_((I,a),(J,b))(A_ab)`, is a
   homomorphism lifting the block inclusion `E_N(M_2(R)) ⊆ E_(2N)(R)`. Put `D = β ∘ St_N(Ψ^(-1))`.
2. **Doubling is stably conjugate to stabilization.** Let `T` be the `2N × N` matrix `diag(t, …, t)`, and `S` the
   `N × 2N` matrix `diag(s, …, s)`, where `t = (t_1, t_2)^T` and `s = (s_1, s_2)`. Then `ST = I_N` and `TS = I_(2N)`.
   - `U = [[T, 0],[0, S]] ∈ GL_(3N)(R)` has `U (g ⊕ I_(2N)) U^(-1) = D(g) ⊕ I_N`.
   - For the stable maps, `stab ∘ D = c_U ∘ stab` as homomorphisms `St_N(R) -> St(R)`. Here `c_U` is the
     conjugation action of `GL(R)` on `St(R)`.
3. **Consequences for `K_2`.** Let `ι_N : K_2(N,R) -> K_2(R)` be stabilization.
   - (a) `ι_(2N) ∘ D = ι_N` on `K_2(N,R)`.
   - (b) If `β` is injective on `K_2(N, M_2(R))` and `ι_(2N)` is injective, then `ι_N` is injective.
   - (c) If `β` restricts to a bijection `K_2(N, M_2(R)) -> K_2(2N, R)`, then `ι_N` is injective if and only if
     `ι_(2N)` is. `D` then identifies `ker ι_N` with `ker ι_(2N)`.
4. **Open.** Whether `β` is injective or bijective on `K_2`, and whether any `ι_M` is injective, for `R = R_L`.

## Reading

- The Morita shift does not by itself prove injective stability. It only moves the question between the levels
  `N` and `2N`: upward by (b), or across by (c). An absolute input at some level is still needed.
- No nontrivial element of `ker ι_N` was found. So the naive route to gate 1 is not refuted.
- The stable side, computing `K_2(R_L)` through Pimsner-type machinery, is lane gq-infinite-primes'.
