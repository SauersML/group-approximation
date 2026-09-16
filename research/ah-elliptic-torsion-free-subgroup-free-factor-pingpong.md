---
rg: 2
id: ah-elliptic-torsion-free-subgroup-free-factor-pingpong
kind: route
title: Conjugate a loxodromic axis off every P-translate, bound the bad translates by acylindricity, then play ping-pong with a large power
target: ah-elliptic-torsion-free-subgroup-is-free-factor
requires: []
artifacts:
  - research/artifacts/thompson-t-disjoint-pair-witness-obstructions-2026-09-16.md
---

The full proof with all constants is in the artifact, §3 (Steps A1–A4). It uses only
Osin's definition of acylindricity and standard facts about Gromov products, boundaries,
the Morse lemma and the ping-pong lemma (Bridson–Haefliger III.H, de la Harpe II.24). Those
facts are listed there as (H1)–(H8) and were not re-read. Fix `o ∈ S` and
`D ≥ diam(P·o)`.

1. **A1: boundary stabilizers in `P` are trivial.** Let `g` be loxodromic and
   `q ∈ P` fix `g^+`. Then `q` moves the whole orbit ray `g^m o`, `m ≥ 0`, by at most a
   constant `ε_A` depending only on `D`, `δ` and the Morse constant of `g`. This follows
   from comparing `[o, g^n o]` with `q[o, g^n o]`, using `(g^n o|q g^n o)_o → ∞`. By
   acylindricity, applied at `o` and a far point `g^m o`, `Stab_P(g^+)` is finite, hence
   trivial.
2. **A2: conjugating away swaps.** Let `g, h` be independent loxodromics and
   `h_n = g^n h g^(-n)`. If for infinitely many `n` some `p_n ∈ P \ {1}` swapped
   `g^n h^+` and `g^n h^−`, then `p_n` would move `g^n o` by a uniformly bounded amount.
   This uses `(g^n h^±|g^n o)_o ≥ d(o, g^n o) − c`, which holds because `g^− ∉ {h^±}`. So
   `p_n` would move every earlier point `g^m o` by a bounded amount `ε_1`. Acylindricity
   leaves finitely many candidates, so one `p ≠ 1` repeats infinitely often and fixes
   `g^+`, contradicting A1. Together with A1 applied to `h_n`: for large `n`, no
   `p ∈ P \ {1}` maps a point of `E = {k^+, k^−}` into `E`, where `k = h_n`.
3. **A3: bad translates are finite, then absent.** If `(pξ|η)_o > r` for `ξ, η ∈ E`, then
   `p` maps the orbit ray of `k` toward `ξ` to within `ε_2 = 4M + 4D + 12δ` of the ray
   toward `η`, up to depth about `r`. For fixed `(ξ, η)` any two such `p, p′` give
   `p′^(-1) p` moving `o` and a far orbit point by at most `ε_3 = 2ε_2 + 2D`. So there are
   at most `4N(ε_3)` bad `p` once `r` is large. Each has `(pξ|η)_o < ∞` by step 2. So for
   some `r_*`, `(pξ|η)_o ≤ r_*` for all `p ∈ P \ {1}` and `ξ, η ∈ E`.
4. **A4: ping-pong.** Let `U` be the set of `x ∈ S ∪ ∂S` with `(x|k^+)_o > ρ` or
   `(x|k^−)_o > ρ`, where `ρ > r_* + D + κ + 2δ`, and `X_1 = ⋃_(p ≠ 1) pU`. Step 3 and the Gromov inequality give
   `X_1 ∩ U = ∅`. North–south dynamics of `k` give `j_0` with `k^i X_1 ⊆ U` for
   `|i| ≥ j_0`. Also `p U ⊆ X_1` for `p ≠ 1`. `P` is infinite and `⟨k^(j_0)⟩ ≅ Z`, so
   the ping-pong lemma gives `⟨P, k^(j_0)⟩ = P * ⟨k^(j_0)⟩`. ∎

**Trust boundary.** The standard hyperbolic-geometry facts (H1)–(H8) are used with generous
constants and were not re-read. The argument only needs every constant to be independent
of `p`, `m` and `n`, and the artifact tracks this at each step. No novelty is claimed. The
abstract of Abbott–Dahmani (arXiv:1610.04143v2, read 2026-09-16) states its property
`P_naive` for elements and hyperbolically embedded subgroups, not for elliptic subgroups,
so the proof was written out rather than imported.
