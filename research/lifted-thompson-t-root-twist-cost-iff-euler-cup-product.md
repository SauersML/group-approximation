---
rg: 2
id: lifted-thompson-t-root-twist-cost-iff-euler-cup-product
kind: claim
title: "The twist cost of T-bar satisfies c(theta) >= const * sqrt|theta|, and this square-root rate is attained along some theta -> 0 iff the real Euler class of Thompson's T is a cup product b_1 ∪ b_2 of two 1-cocycles in an orthogonal representation of T; in that case c(theta) is of order sqrt|theta| and T-bar has the Haagerup property"
distinct_from:
  lifted-thompson-t-relative-t-forces-dyadic-twist-gap: that defines c and proves the linear floor c >= |e(theta)-1|/L; this proves the square-root floor from a second-order expansion and identifies exactly when the floor is sharp
  lifted-thompson-t-is-a-t-menable: that is the target; this gives it a one-prerequisite sufficient condition (e_R in the Kahler subspace of H^2(T;R)) that mentions only Thompson's T, and shows that condition is also necessary for the optimal twist rate
  lifted-thompson-t-center-has-relative-t: that is inf c > 0; this is about the rate at which c can tend to 0, and shows that relative (T) of the centre forces e_R outside the Kahler subspace
---

**ESTABLISHED** by `lifted-thompson-t-root-twist-cost-iff-euler-cup-product-proof`.

## Notation

- `T̄`, `z`, `p : T̄ → T`, the finite symmetric generating set `S` of `T̄`, `e(θ) = exp(2πiθ)`
  and the twist cost `c : R/Z → [0, 2]` are as in
  `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`. `‖θ‖` is the distance from `θ` to `Z`.
- Fix a section `σ : T → T̄` with `σ(1) = 1`. The *Euler cocycle* `ε : T × T → Z` is defined by
  `σ(g)σ(h) = z^{ε(g,h)} σ(gh)`, and `e_R ∈ H²(T; R)` is its real class. Coboundaries are
  `(dβ)(g,h) = β(g) + β(h) − β(gh)`.
- For a unitary representation `π` of `T` on a complex Hilbert space (inner product linear in the
  second slot) and a 1-cocycle `b`, i.e. `b(gh) = b(g) + π(g)b(h)`, the *area cocycle* is
  `ω_b(g,h) = Im⟨b(g), π(g)b(h)⟩`.
  - It is a real 2-cocycle on `T`: twice the symplectic area of the triangle with vertices `0`,
    `b(g)`, `b(gh)` of the affine action.
- The *Kähler subspace* `V_T ⊆ H²(T; R)` is the set of classes `[ω_b]` over all such `(π, b)`.
- For an orthogonal representation `π` on a real Hilbert space and 1-cocycles `b_1, b_2`, the cup
  product is `(b_1 ∪ b_2)(g,h) = ⟨b_1(g), π(g) b_2(h)⟩`.
- Let `m` be the length of a word `w` in the alphabet `S` that represents `z` and has exponent sum
  `0` in every letter. It exists because `T̄` is perfect.

## Statement

- **(0) The Kähler subspace.** `V_T` is a linear subspace of `H²(T; R)`. It equals the set of
  cup-product classes `[b_1 ∪ b_2]`, over orthogonal representations `π` of `T` and pairs
  `b_1, b_2` of 1-cocycles into the same `π`.
- **(1) Square-root floor.** Let `π` be a unitary representation of `T̄` with `π(z) = e(θ)·I`, and
  let `ξ` be a unit vector. Then `|e(θ) − 1| ≤ (m²/2) · max_{s∈S} ‖π(s)ξ − ξ‖²`. Hence
  `c(θ) ≥ √(2|e(θ) − 1|)/m ≥ 2√(2‖θ‖)/m` for every `θ`.
- **(2) Kähler lift.** If `e_R ∈ V_T`, then:
  - there is `C` with `c(θ) ≤ C √‖θ‖` for all `θ`;
  - `T̄` has the Haagerup property, so `lifted-thompson-t-is-a-t-menable` holds.
- **(3) Converse at the square-root rate.** If
  `liminf_{θ→0, θ≠0} c(θ)/√‖θ‖ < ∞`, then `e_R ∈ V_T`.

**Dichotomy.** Exactly one of the following holds.
- `e_R ∈ V_T`. Then `c(θ) ≍ √‖θ‖` near `0`, and `T̄` is Haagerup.
- `e_R ∉ V_T`. Then `c(θ)/√‖θ‖ → ∞` as `θ → 0`.

This is a quantitative sharpening of the superlinearity result of wave 11
(lifted-thompson-t-twist-cost-is-superlinear, not present in this worktree's base). That result
says `c(θ)/‖θ‖ → ∞`. Here the floor is `√‖θ‖`, and it is sharp exactly on the Kähler branch.

## Role

- *New decomposition of the target, with one prerequisite that can fail on its own.* The target
  follows from **(K)**: `e_R = [b_1 ∪ b_2]` for some orthogonal representation of Thompson's `T`
  and two of its 1-cocycles.
  - (K) mentions only `T`.
  - (K) fails for central extensions whose centre has relative (T). By (2) it also fails whenever
    the twist cost is not `O(√‖θ‖)`. By (3) it holds as soon as `c(θ_n) = O(√‖θ_n‖)` along a
    single sequence `θ_n → 0`.
- *What it tells a breaker.* Refuting the target now needs more than killing (K). The
  intermediate regime `√‖θ‖ ≪ c(θ)`, with `c(2^{-k})` still square-summable, remains open for
  the dyadic test.
- *What it tells a prover.* The most economical witness is forced to be a Weyl–Fock (Gaussian with
  phases) lift of a single cocycle pair of `T` whose area cocycle is the Euler cocycle, up to a
  coboundary.
  - Real cocycles alone never work: for a real cocycle into a complexified orthogonal
    representation, `ω_b = 0`. So Farley's cubical cocycle on its own contributes nothing. A
    second, independent cocycle in the same representation is needed.
- *Model case.* For a closed surface group `Γ` with the Euler class of a hyperbolic structure,
  (K) holds, even with trivial coefficients (`e_R` is a sum of cup products of classes in
  `H¹(Γ; R)`). This matches the known Haagerup property of the lifted surface group.
  - The experiment `experiments/twist-cost-2026-09-17/second_order_checks.py` checks that the
    Heisenberg (clock and shift) relation meets the floor of (1) in order: both scale as `n^{-1/2}`,
    within a factor of 2.

## Relation to the measurable-splitting route

The wave-9 route lifted-thompson-t-a-t-menable-via-measurable-euler-splitting (not in this
worktree's base) asks for a measurable real Euler splitting over a nonsingular `T`-space. This
route is different in kind:
- it asks for a unitary cocycle whose area cocycle is the Euler cocycle;
- that cocycle is lifted through Weyl operators on Fock space;
- the central element acts by a genuine phase, so no splitting is required.

## Not claimed

- Whether `e_R ∈ V_T` for Thompson's `T`. This is the one open prerequisite of the new route.
- Anything about the regime between `√‖θ‖` and the square-summability threshold of the dyadic test.
- That the Weyl–Fock representations in (2) lie outside the Bernoulli/Gaussian class killed in wave
  11 (thompson-t-bernoulli-euler-splittings-need-amenable-f, not in this worktree's base) is argued
  only informally:
  - that kill concerns pmp Gaussian actions with an `S^1`-valued cocycle;
  - on the Kähler branch, the translation part of the affine action is nonzero and the Gaussian
    action is only nonsingular;
  - this is not written out as a proof.

Derivation: route `lifted-thompson-t-root-twist-cost-iff-euler-cup-product-proof`.
