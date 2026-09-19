---
rg: 2
id: cup-products-of-integrably-paired-potential-cocycles-are-exact
kind: claim
title: "If a 1-cocycle b_1 into a Koopman representation is the coboundary of a measurable potential f that pairs integrably with every value of a second cocycle b_2, then b_1 ∪ b_2 = dN with N(g) = ∫ conj(f) b_2(g); so no Kähler witness for the Euler class of Thompson's T comes from measured walls, cube complexes or integrable-potential Koopman cocycles"
distinct_from:
  lifted-thompson-t-root-twist-cost-iff-euler-cup-product: that reduces T-bar Haagerup to (K), e_R in the Kahler subspace V_T, and notes that a single real cocycle has area 0; this proves that pairs of cocycles with integrably paired potentials in one Koopman model (all wall and cubical cocycles, complex combinations included) have exact cup product, killing that whole witness class for (K)
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that kills cocycles of T-bar in representations with a circle PVM; this is about 1-cocycles of T and the cup-product class in H^2(T;R), and works for every nonsingular Koopman model, over the circle or not
  lifted-thompson-t-convex-line-walls-are-trivial: that kills T-bar-invariant order-convex wall structures on the line; this kills the use of any T-invariant measured wall structure (or pair of them in one wall space) as a source of the Kahler area class
artifacts: []
---

**ESTABLISHED** by `integrably-paired-cup-products-exact-proof`.

## Setting

- `G` is a countable group. `(Ω, μ)` is a σ-finite measure space with a nonsingular action of `G`.
  The Koopman representation on `L²(Ω, μ)` (real or complex) is
  `(π(g)u)(x) = u(g⁻¹x) · (d(g_*μ)/dμ)(x)^{1/2}`. The same formula defines `π(g)` on all
  measurable functions.
- Inner products are conjugate-linear in the first slot. The cup product of 1-cocycles `b_1, b_2`
  into `π` is `(b_1 ∪ b_2)(g,h) = ⟨b_1(g), π(g) b_2(h)⟩`. The area cocycle of one complex cocycle is
  `ω_b = Im(b ∪ b)`. Coboundaries are `(dN)(g,h) = N(g) + N(h) − N(gh)`.
- A *potential* for `b_1` is a measurable function `f` on `Ω` with `b_1(g) = π(g)f − f` for all `g`.
  `f` itself need not be square-integrable.

## Statement

**(A) Pairing lemma.** Let `b_1` have a potential `f`, and let `b_2` be any 1-cocycle into `π`
such that `f̄ · b_2(g) ∈ L¹(μ)` for every `g ∈ G` (integrable pairing). Then

  `b_1 ∪ b_2 = dN`, where `N(g) = ∫_Ω f̄ · b_2(g) dμ`.

So `[b_1 ∪ b_2] = 0` in `H²(G; R)` (or `H²(G; C)`). If `b` has a potential `f` with
`f̄ · b(g) ∈ L¹` for all `g`, then `ω_b = d(Im N)`.

**(B) What dies for Thompson's `T`.** Apply (A) with `G = T`. In each of the following families
every cup-product class and every area class is `0` in `H²(T; R)`. So none of them witnesses (K)
(`lifted-thompson-t-euler-class-in-kahler-subspace`) unless `e_R = 0`. That `e_R ≠ 0` is recalled
from Ghys–Sergiescu and is not re-verified here; the kill does not depend on it.

1. *Measured walls.* Any pair of cocycles `b_i(g) = 1_{σ(g x_i)} − 1_{σ(x_i)}` of one
   `T`-invariant measured wall structure (the half-space space with its invariant measure, base
   points `x_1, x_2`, or `T`-invariant sub-families of walls), and every complex linear combination
   of finitely many such cocycles. Potentials are bounded and values have finite measure.
2. *Cube complexes and commensurating actions.* In particular every pair of cocycles from one
   action of `T` on a CAT(0) cube complex or one commensurated subset system, Farley's proper
   action included.
3. *Integrable potentials.* Every pair in one nonsingular Koopman model with a potential of `b_1` in
   `L^p` and values of `b_2` in `L^{p'}` (`1/p + 1/p' = 1`, `1 ≤ p ≤ ∞`).
4. *Countable disjoint unions* of such models, as long as the summed pairing
   `Σ_n ∫ |f^{(n)}| |b_2^{(n)}(g)|` is finite, since a direct sum of Koopman representations is the
   Koopman representation of the disjoint union.

The class is **not** killed if the two cocycles live in different wall structures that are placed
in orthogonal summands. Then the cup product is `0` for a trivial reason. So combining different
wall spaces does not help either.

## Named invariant and the step where every member dies

- **Invariant.** The renormalized pairing (intersection number) `N(g) = ∫ f̄ · b_2(g) dμ`. For
  indicator potentials it is the signed count `μ(A ∩ gB∖B) − μ(A ∩ B∖gB)` of commensurated sets
  `A, B`.
- **Step.** The expansion `⟨π(g)f − f, π(g)b_2(h)⟩ = P(f, b_2(h)) − P(f, b_2(gh) − b_2(g))`, which
  uses only the `G`-invariance of the pairing `P(u, v) = ∫ ū v dμ` on absolutely integrable pairs.
  It turns the area cocycle into `dN`.
- **Why the Euler class escapes (calibration).** The proof also shows that `e_R` of `T` is the
  symplectic area class of the displacement cocycle `u_g = g̃ − id` in the space of 1-periodic
  functions, `ε ~ −∫_0^1 (u_g ∘ h̃) du_h`. That cocycle has the potential `x ↦ x`. This potential
  is *not* periodic: it lives on the `Z`-cover, and its pairing with periodic functions is not
  `T`-invariant. The defect is exactly the winding. So a (K)-witness has to encode a potential that
  winds, in the sense that no Koopman model makes it pair integrably and invariantly with the other
  cocycle.
- For surface groups (calibration world where (K) holds), the classes come from homomorphisms to
  `R`. Their potentials are the unbounded coordinates of line trees, and no integrable pairing
  exists, consistent with (A).

## Consequence for the route

`lifted-thompson-t-root-twist-cost-iff-euler-cup-product` reduces `lifted-thompson-t-is-a-t-menable`
(necessary for `brin-thompson-groups-nv-are-a-t-menable`) to (K). This claim removes, as a source of
(K), every piece of the Haagerup machinery that proves `T` Haagerup (Farley's cubical action and
every measured wall structure). A witness must be a cocycle pair with no integrably paired potential
in any common Koopman model. In the Fock picture, the one-particle cocycle must be *genuinely
non-Koopman-potential*, like the winding displacement.

Derivation: route `integrably-paired-cup-products-exact-proof`.
