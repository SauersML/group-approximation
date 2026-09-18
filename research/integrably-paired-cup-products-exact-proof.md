---
rg: 2
id: integrably-paired-cup-products-exact-proof
kind: route
title: The invariant pairing of the potential with the second cocycle turns the cup product into the coboundary of the renormalized intersection number; wall, cubical and integrable Koopman cocycles all have such potentials; the Euler class is the area of the displacement cocycle, whose potential winds
target: cup-products-of-integrably-paired-potential-cocycles-are-exact
requires: []
artifacts: []
---

Notation is that of the target. The proof is self-contained; the only imported facts are the
standard change of variables for nonsingular actions and the definition of a measured wall
structure (Cherix–Martin–Valette, *Ergodic Theory Dynam. Systems* 24 (2004), §1; recalled, not
used beyond the definition below).

## Step 0. The invariant pairing

For measurable `u, v` on `Ω` with `ū v ∈ L¹(μ)` put `P(u, v) = ∫ ū v dμ`.

- (P1) `P` extends the inner product of `L²(Ω, μ)`.
- (P2) If `ū v ∈ L¹`, then `\overline{π(g)u} · π(g)v ∈ L¹` and `P(π(g)u, π(g)v) = P(u, v)`.
  Indeed `\overline{π(g)u}(x) π(g)v(x) = ū(g⁻¹x) v(g⁻¹x) · (d(g_*μ)/dμ)(x)`, and
  `∫ φ(g⁻¹x) (d(g_*μ)/dμ)(x) dμ(x) = ∫ φ(g⁻¹x) d(g_*μ)(x) = ∫ φ(y) dμ(y)` for `φ ∈ L¹`, by
  the definition of the Radon–Nikodym derivative and of `g_*μ`, applied to `|φ|` and then to `φ`.
- (P3) `P` is additive in each slot on pairs where all terms are integrable.

## Step 1. The pairing lemma (A)

Let `b_1(g) = π(g)f − f` and let `f̄ · b_2(k) ∈ L¹` for all `k`. Fix `g, h`.

1. `b_1(g) ∈ L²` and `π(g)b_2(h) ∈ L²`. By (P1),
   `⟨b_1(g), π(g)b_2(h)⟩ = P(π(g)f − f, π(g)b_2(h))`.
2. Both pieces are integrable:
   - `\overline{π(g)f} · π(g)b_2(h)` is integrable by (P2) applied to `f̄ b_2(h) ∈ L¹`;
   - `f̄ · π(g)b_2(h) = f̄ · (b_2(gh) − b_2(g))` is a difference of two integrable functions, by the
     cocycle identity `b_2(gh) = b_2(g) + π(g)b_2(h)`.
3. So by (P3), (P2) and the cocycle identity,
   `⟨b_1(g), π(g)b_2(h)⟩ = P(f, b_2(h)) − P(f, b_2(gh)) + P(f, b_2(g)) = N(g) + N(h) − N(gh)`,
   with `N(k) = P(f, b_2(k))`.

This is `b_1 ∪ b_2 = dN`. For a single complex cocycle `b` with potential `f` and
`f̄ b(k) ∈ L¹`, take `b_1 = b_2 = b` and imaginary parts: `ω_b = d(Im N)`. For real
representations the same lines hold with `P(u,v) = ∫ uv dμ`. ∎(A)

## Step 2. The families of (B)

1. **Measured walls.** A measured wall structure on a `T`-set `X` gives a `σ`-finite measure space
   `(Ω, μ)` of half-spaces with a measure-preserving `T`-action, and for `x ∈ X` the set
   `σ(x) ⊆ Ω` of half-spaces containing `x`, with `σ(gx) = gσ(x)` and
   `μ(σ(x) Δ σ(y)) = 2 d_μ(x, y) < ∞`. The Koopman representation is the permutation action
   `u ↦ u ∘ g⁻¹`. The cocycle `b_x(g) = 1_{σ(gx)} − 1_{σ(x)} = π(g) 1_{σ(x)} − 1_{σ(x)}` has the
   bounded potential `1_{σ(x)}` and values in `L¹ ∩ L²`.
   - For `T`-invariant measurable sub-families `Ω' ⊆ Ω` replace `σ(x)` by `σ(x) ∩ Ω'`.
   - A finite complex combination `b = Σ a_k b_{x_k}^{Ω_k}` has the bounded potential
     `Σ a_k 1_{σ(x_k) ∩ Ω_k}` and values in `L¹`.
   - So for any two such cocycles `b_1, b_2`, `f̄ b_2(g)` is (bounded) × (`L¹`), hence integrable,
     and (A) applies.
2. **Cube complexes and commensurated sets.** An action on a CAT(0) cube complex, or a
   commensurated subset `A` of a `T`-set, is a measured wall structure with counting measure
   (half-spaces, resp. `Ω = X` and `σ = gA`); Step 2.1 applies. This covers Farley's action.
3. **`L^p` potentials.** If `f ∈ L^p(μ)` and `b_2(g) ∈ L^{p'}(μ)`, Hölder gives `f̄ b_2(g) ∈ L¹`.
4. **Disjoint unions.** `⊕_n L²(Ω_n, μ_n) = L²(⊔_n Ω_n, ⊔ μ_n)` equivariantly, so (A) applies on
   the union under the summed hypothesis.

For wall cocycles placed in orthogonal summands (different wall spaces), `b_1 ∪ b_2 = 0` pointwise.

## Step 3. The Euler class as the area of a winding potential (calibration)

Let `T̄` act on `R` by lifts, `z(x) = x + 1`. For `f̃ ∈ T̄` put `u_f = f̃ − id`. It is 1-periodic,
PL and `|u_f(x) − u_f(y)| < 1`: for `x < y < x + 1`, monotonicity and `f̃(x+1) = f̃(x) + 1`
give `0 < f̃(y) − f̃(x) < 1`, so `u_f(y) − u_f(x) ∈ (−1, 1)`, and periodicity extends this to all
`x, y`. Define `A(f̃) = ∫_0^1 u_f(x) dx`.

1. `A(z^k f̃) = A(f̃) + k`.
2. `A(f̃ g̃) = ∫_0^1 (f̃(g̃x) − g̃x) dx + ∫_0^1 (g̃x − x) dx = A(g̃) + ∫_0^1 u_f(g̃x) dx`, so
   `A(f̃g̃) − A(f̃) − A(g̃) = D(f, g) := ∫_0^1 (u_f(g̃x) − u_f(x)) dx`, with `|D| < 1`. `D` depends
   only on the images `f, g ∈ T`, since `u_{zf} = u_f + 1`.
3. With the section `σ` and `σ(f)σ(g) = z^{ε(f,g)}σ(fg)`, apply `A`:
   `ε(f,g) + A(σ(fg)) = A(σ(f)) + A(σ(g)) + D(f,g)`. So `ε = D + dβ` with `β = A ∘ σ`, and
   `e_R = [D]`.
4. For 1-periodic PL `φ, ψ` put `ω(φ, ψ) = ∫_0^1 φ dψ`. Then `ω(φ∘g̃, ψ∘g̃) = ω(φ, ψ)`, since
   `g̃` maps `[0,1]` onto an interval of length 1. And
   `ω(u_f∘g̃, u_g) = ∫_0^1 u_f(g̃x) d(g̃x) − ∫_0^1 u_f(g̃x) dx = ∫_0^1 u_f − ∫_0^1 u_f∘g̃ = −D(f,g)`.
5. `u_{fg} = u_f ∘ g̃ + u_g`: `u` is a 1-cocycle for the right action `φ · g = φ ∘ g̃` on periodic
   functions modulo constants. Its potential is `id`: `u_g = id · g − id`. So `e_R = −[ω(u·, u)]`
   is the symplectic area class of a cocycle whose potential `id` is not periodic.
6. The argument of Step 1 with `P = ω` breaks at exactly one point: `ω(id∘g̃, ψ∘g̃) ≠ ω(id, ψ)` in
   general (the difference is `∫_0^1 u_g dψ∘g̃`, and `id` is not periodic, so the change of
   variables of (P2) fails). This is the winding. The pairing lemma is sharp in this sense.

The inequality in Step 3 is used only to see `|D| < 1` (so `D` is the bounded Euler cocycle); the
identity `e_R = [D]` does not use it.
