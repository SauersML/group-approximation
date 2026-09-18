---
rg: 2
id: smart-renormalization-admits-no-graded-basins
kind: claim
title: SMART's height-3 renormalization cannot be graded, even after any finite skew-product decoration, so it does not yield the ternary Toeplitz factor that would put a periodic group in 2V
requires:
  - smart-induced-map-has-brick-local-height-3-renormalization
  - graded-renormalization-gives-ternary-toeplitz-factor
distinct_from:
  graded-renormalization-gives-ternary-toeplitz-factor: that gives the sufficient condition (a clopen colouring cycled by the renormalization); this shows SMART's renormalization fails it.
  smart-induced-map-alternates-head-direction: that finds the Z/2 eigenvalue carried by the head direction; this shows no Z/3 grading of the renormalization exists, because the attractor of the zero insertion is approached from all three depth classes.
---

**ESTABLISHED** (lane proof below, bh-free-01, elementary, not independently reviewed). It uses only the
landed renormalization table.

## Setting

`U` is SMART's moving-tape map induced on its genuine level-0 moves `Y`. `A ⊆ Y` is the set of first
`Y`-points of level-1 moves, and `φ : A → Y` is the brick-local homeomorphism with `φ ∘ U³ = U ∘ φ` and
`Y = A ⊔ UA ⊔ U²A`, all as in `smart-induced-map-has-brick-local-height-3-renormalization`. Put
`Ψ = φ^{-1} : Y → A`. Then `(Y, U, D = A, Ψ)` satisfies (R1) and (R2) of
`graded-renormalization-gives-ternary-toeplitz-factor`.

## Statement

1. **SMART itself.** There are no clopen `L_0, L_1, L_2` partitioning `Y` that satisfy (R3) and (R4) for
   this `Ψ`.
2. **Finite decorations.** Let `K` be finite and `τ : Y → Sym(K)` locally constant. Let
   `Ũ(y, κ) = (U y, τ(y)κ)` on `Ỹ = Y × K`. Let `Ψ̃` be any homeomorphism `Ỹ → A × K` that lifts `Ψ` and
   satisfies (R2) for `Ũ`. Then again no clopen colouring of `Ỹ` satisfies (R3) and (R4).

## Proof

Let `z_k` be the configuration with state `▶_2` on a cell holding `1`, then `0^k`, then `1`, and a fixed
tape everywhere else.
- `z_k ∈ Y`, since `▶_2` sits on a nonzero cell.
- For `k ≥ 1`, `z_k` is the start of `M_b(k)`, hence of its first level-1 descendant `M_b(1)`. So `z_k ∈ A`,
  and the first case of the table ("at a start of `M_b(1)`, delete the `0` right of the head") gives
  `φ(z_k) = z_{k−1}`. That is, `z_k = Ψ^k(z_0)`.
- `z_0 ∉ A`. The four cases of the table describe `A`. `z_0` has a nonzero right neighbour, so it is not a
  start of `M_b(1)`. Its head cell is `1`, not the written `2`, so it is not the first `Y`-point of
  `M_p(1)`. The `M_d(1)` and `M_q(1)` cases require a left-moving state. Hence `z_0 ∈ Y ∖ A = UA ⊔ U²A`.
- `z_k → z_∞`, the configuration with `▶_2` on `1` followed by `0^∞`, and `z_∞ ∈ Y`.

**Item 1.** By (R3), `z_0 ∈ L_0`. By (R4), `z_k ∈ L_{k mod 3}`. The clopen set `L_c` that contains `z_∞`
contains `z_k` for all large `k`, which contradicts `z_k ∈ L_{k mod 3}`.

**Item 2.** `Ψ̃` is a homeomorphism `Ỹ → A × K` lifting `Ψ`, so it maps the fibre over `z_k` bijectively
onto the fibre over `z_{k+1}`. The whole fibre over `z_0` lies in `(UA ⊔ U²A) × K = Ũ(A×K) ⊔ Ũ²(A×K)`, hence
in `L̃_0` by (R3). By (R4) and induction, the whole fibre over `z_k` lies in `L̃_{k mod 3}`. `K` is finite,
so some `(z_∞, κ)` is a limit of points `(z_k, κ_k)` with `k` in every residue class. This contradicts
clopenness, as before.

## Reading

- *What fails.* The attractor of the zero insertion `Ψ` is approached through configurations of every depth.
  In the language of Lemma A of `graded-renormalization-gives-ternary-toeplitz-factor`, the odometer factor
  is open there (heuristic; not proved here). Recolouring registers do not help, because they are carried along the same approach.
- *What a positive construction needs.* A graded renormalization must see the depth modulo 3 at bounded
  range, even at points of infinite depth. So a host has to store a continuous `Z_3`-valued depth that
  extends to the holes.
  - One candidate: a counter that counts its own carry length in 3-adic digits. It avoids the fixed points
    of naive positional counters, since an infinite carry runs an odometer on the depth register. But
    incrementing that register raises the same problem one level up.
  - This is recorded as the open design problem `some-nv-element-has-a-graded-height-3-renormalization`.
