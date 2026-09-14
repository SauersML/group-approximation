---
rg: 2
id: modular-matrix-failure-descent-proof
kind: route
title: Enlarge the matrix size, pass to the field of q-th roots of unity, and read M_r(F[G]) as a direct factor of F_p[G × P]
target: modular-matrix-failures-descend-to-scalars-over-g-times-p
requires:
  - linear-strict-pairs-are-transposes-of-post-surjective-automata
artifacts:
  - research/artifacts/gk3-binary-descent-2-2026-09-14.md
---

**Standard facts used** (textbook, not re-pinned): Maschke's theorem (`F_p[P]` is semisimple when
`p ∤ |P|`); the Artin–Wedderburn theorem; Wedderburn's little theorem (finite division rings are fields).

**Ring facts.**
- If `R ⊆ S` is a unital subring and `ab = 1 != ba` in `R`, the same holds in `S`.
- If `S = S_1 × S_2` and `ab = 1 != ba` in `S_1`, then `(a,1)(b,1) = (1,1)` and `(b,1)(a,1) = (ba,1) != (1,1)`.
- Conversely, if `ab = 1 != ba` in a finite product of rings, some factor is not directly finite.

## (1) ⇒ (2)

1. **Enlarge `n`.** Fix primes `q, r` different from `p` with `r >= n`. The map `a ↦ diag(a, I_(r-n))` is a
   unital injective ring map `M_n(F_p[G]) → M_r(F_p[G])`, so `M_r(F_p[G])` is not directly finite.
2. **Roots of unity.** Let `F = F_p(ζ)`, with `ζ` a primitive `q`-th root of unity, which exists in a finite
   extension of `F_p` because `q != p`. Since `M_r(F_p[G]) ⊆ M_r(F[G])` unitally, `M_r(F[G])` is not directly
   finite.
3. **The group.** Put `P = N ⋊ ⟨c⟩` with `N = (C_q)^r` and `c` permuting coordinates cyclically, so
   `|P| = q^r r` is prime to `p`. Define `ρ: P → GL_r(F)`:
   - the generator of the `j`-th factor of `N` goes to `t_j = diag(1, ..., ζ, ..., 1)` (`ζ` in place `j`);
   - `c` goes to the permutation matrix with `c e_k = e_(k+1)` (indices mod `r`).

   Then `c t_j c^(-1) = t_(j+1)`, which matches the action of `c` on `N`, so `ρ` is a homomorphism.
4. **`ρ` is onto as an algebra map.** Let `A` be the `F_p`-span of `ρ(P)`, an `F_p`-subalgebra of `M_r(F)`.
   - Choose `f ∈ F_p[x]` with `f(ζ) = (ζ - 1)^(-1)`; it exists because `F_p[ζ]` is a field and `ζ != 1`.
   - Then `f(t_1)(t_1 - I) = E_11`, so `E_11 ∈ A`. Also `t_1^i E_11 = ζ^i E_11 ∈ A`, and `F = F_p[ζ]`, so
     `F·E_11 ⊆ A`.
   - Conjugating by powers of `c` gives `F·E_jj ⊆ A` for every `j`, and `E_jj c^m = E_(j, j-m)` gives every
     `F·E_(jk) ⊆ A`.

   So `A = M_r(F)`, and `ρ` extends to a surjective `F_p`-algebra map `F_p[P] → M_r(F)`.
5. **Direct factor.** `F_p[P]` is semisimple, so `F_p[P]` is a finite product of simple rings, and the
   maximal ideal `ker ρ` is the product of all factors but one. Hence `F_p[P] ≅ M_r(F) × B` as rings.
6. **Tensor.** `F_p[G × P] ≅ F_p[G] ⊗_(F_p) F_p[P] ≅ (F_p[G] ⊗ M_r(F)) × (F_p[G] ⊗ B)`, and
   `F_p[G] ⊗_(F_p) M_r(F) ≅ M_r(F[G])`. By step 2 and the ring facts, `F_p[G × P]` is not directly finite.

## (2) ⇒ (1)

- By Maschke, Artin–Wedderburn and Wedderburn's little theorem, `F_p[P] ≅ ∏_i M_(r_i)(F_i)` with finite
  fields `F_i ⊇ F_p`. So `F_p[G × P] ≅ ∏_i M_(r_i)(F_i[G])`, and some factor `M_(r_i)(F_i[G])` is not directly
  finite.
- Fix an `F_p`-basis of `F_i`, of size `e_i`, and let `L: F_i → M_(e_i)(F_p)` be the regular representation.
  The map `Σ_g a_g g ↦ Σ_g L(a_g) g` is a unital injective ring map `F_i[G] → M_(e_i)(F_p[G])`, because the
  matrices `L(a)` have entries in `F_p` and commute with group elements.
- Hence `M_(r_i)(F_i[G]) ⊆ M_(r_i e_i)(F_p[G])` unitally, and the larger ring is not directly finite.

## Automaton form

`linear-strict-pairs-are-transposes-of-post-surjective-automata` (item 2, over `k = F_p`) says: an
`F_p`-linear automaton over `F_p^n` on a group `H` is injective and not surjective iff
`M_n(F_p[H])` contains `dc = I_n != cd` for its matrix `c`. By item 3, some such automaton exists iff some
`M_n(F_p[H])` is not directly finite. Apply this with `H = G` and with `H = G × P`, `n = 1`.

An `F_(p^d)`-linear automaton over `F_(p^d)^n` is `F_p`-linear over `F_p^(nd)` after choosing a basis, so it
reduces to the `F_p` case.
