---
rg: 2
id: binary-cyclic-corner-state-criterion-proof
kind: route
title: Halving towers push complement absorption into the corner, and the second halving map pulls states back
target: binary-cyclic-corner-full-iff-complement-corner-has-no-state
requires: []
artifacts:
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

Artifact Theorem B, a complete direct proof. The one outside input is the classical state criterion for a
unital ring: a state on `(K_0(T), [T])` exists iff `[T]` is not `<= 0`. It is proved by Hahn–Banach in
Section 2 of `research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md`.

1. **Halving homomorphisms (Lemma 1.1).** `D(G)` commutes with `g`, so `ψ(x) = e D(x)` and
   `ψ'(x) = (1 - e) D(x)` are unital ring homomorphisms into `eAe` and `T`.
2. **Tower (Lemma 1.2).**
   - Conjugating by the `GL_2(F_3)` permutation units of the nine cylinders gives `[fA] = 3 d_1`.
   - `ψ` gives `d_k = 3 d_(k+1)`.
   - The orthogonal decomposition of `e` gives `[eA] = p_(k+1) + ((3^k - 1)/2) d_k`.
3. **Fullness is a class inequality (Lemma 1.3):** `c e b = 1` iff `[A] <= [eA]`.
4. **1 => 3 => 4.** `[A] + x = [eA]` gives `[fA] + x = 0` in `K_0`.
5. **4 => 5.** A state `s_T` on `T` pulls back along `ψ'` to a state of `A` with value `2/3` at `[f]`,
   because `ψ'(f) = f_(K_3) + f_(K_4)` and the three `f_K` inside `f` are equivalent in `T`.
6. **5 <=> 6.** The state criterion.
7. **6 => 1.**
   - Absorption `N v + v + q = N v` in `V(A)` iterates to `N v + 3^k v + 3^k q = N v`.
   - Applying `F^k` gives `N d_k + v + x = N d_k`.
   - `[eA] = N d_k + c` once `(3^k - 1)/2 >= N`, so `[eA] + [fA] + x = [eA]`.
