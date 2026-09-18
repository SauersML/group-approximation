---
rg: 2
id: thompson-t-co-amenable-subgroup-kills-real-euler-class
kind: claim
title: "Thompson's T has a co-amenable subgroup H on which the real Euler class vanishes (equivalently, the preimage of H in T-bar has a homomorphism to R sending z to 1)"
distinct_from:
  thompson-t-euler-class-splits-over-almost-invariant-space: that allows any nonsingular T-space; this is its special case X = T/H with counting measure, reduced to a statement about subgroups
  thompson-t-orbits-carry-no-invariant-means: that shows point stabilizers (e.g. F) are not co-amenable in T; this asks for a co-amenable subgroup of a different kind
artifacts: []
---

**Statement.** There is a subgroup `H ≤ T` with both properties:
- `H` is co-amenable in `T`: `T/H` carries a `T`-invariant mean, or equivalently `ℓ²(T/H)` has
  almost invariant vectors.
- The preimage `H̄ ≤ T̄` has a homomorphism `u : H̄ → R` with `u(z) = 1`. Equivalently,
  `e_R|_H = 0` in `H²(H, R)`, where `e_R` is the real Euler class.

**Status.** OPEN.

## Role

This implies `thompson-t-euler-class-splits-over-almost-invariant-space` (proof below), and so
`lifted-thompson-t-is-a-t-menable`.

`H = T` is excluded, because `T̄` is perfect.

**Proof of the implication.** Take `X = T/H = T̄/H̄` with counting measure. Choose a section
`σ : T̄/H̄ → T̄`, and set `β(g, y) = u(σ(gy)^{-1} g σ(y))`. The argument lies in `H̄`.
- The cocycle identity holds by telescoping.
- `β(z, y) = u(σ(y)^{-1} z σ(y)) = u(z) = 1`, since `z` is central.
- The Koopman representation is the quasi-regular representation `ℓ²(T/H)`. It has almost
  invariant vectors iff `H` is co-amenable (Eymard; standard). ∎

## Forced shape (established)

**(D1) `H` has no finite orbit on `S^1`.**

Suppose `H` preserves a finite set. Then a finite-index subgroup `H' ≤ H` fixes a point of `S^1`.
- `H'` is co-amenable in `T`: average an invariant mean on `T/H` over the fibres of
  `T/H' → T/H`, each of size `[H : H']`.
- `u|_{H̄'}` still sends `z` to `1`.
- So `X' = T/H'` is a witness for (MT) with an equivariant map `tH' ↦ t·p` to `S^1`, which
  contradicts (F2) of `thompson-t-euler-class-splits-over-almost-invariant-space`.

This excludes `F` and all point and finite-set stabilizers.

**(D2) `H` is nonamenable, and the induced `β` is not uniformly integrable.**
- `H` is nonamenable because `T` is nonamenable, and a co-amenable amenable subgroup would
  make `T` amenable.
- The induced `β` is not uniformly integrable along any almost invariant sequence, by (F1).

## Attempts

- 2026-09-18 (swarm-0917-w9-w9-nv-follow): isolated; (D1) and (D2) proved. No candidate `H`
  was tested.
  - *Candidate: `H = PSL_2(Z) ≤ T`.*
    - `PSL_2(Z)` embeds in `T`, acting on `S^1` by the Minkowski-conjugated projective action.
      Its preimage in `T̄` is recalled as `B_3`, whose abelianization is `Z`. The centre
      generator `Δ²` maps to `6`, so `u = ab/6` works, and `H` satisfies (D1) and (D2). The
      identification of the preimage with `B_3` was not rechecked verbatim.
    - So "is `PSL_2(Z)` co-amenable in `T`?" is a single falsifiable question. A yes proves
      `lifted-thompson-t-is-a-t-menable`.
  - *Test for a no.* Suppose `H` preserves a probability measure `λ` on a compact `T`-space `Y`
    that carries no `T`-invariant probability. Then `H` is not co-amenable, because integrating
    `t_*λ` against an invariant mean on `T/H` would give a `T`-invariant probability. For
    `PSL_2(Z)`, the space `Y = S^1` gives nothing, since the action is nonelementary.
- 2026-09-18 (swarm-0917-w12-w12-nv-last1): the candidate `H = PSL_2(Z)` is refuted, together
  with every subgroup of every stabilizer of a quad-complete lamination. The node stays OPEN.
  - *Forced shape (D4).* A co-amenable `H` fixes no `τ ∈ Tri_D`, a non-crossing,
    quad-complete chord system with endpoints in a countable `T`-invariant set `D`. This is
    `thompson-t-quad-complete-laminations-carry-no-invariant-mean`, Part 4.
  - (D4) contains the forced shape (D3) that swarm-0917-w10 found on the bus (`H` lies in no
    conjugate of `PSL_2(Z)`). The Minkowski-conjugated `PSL_2(Z)` fixes the dyadic Farey
    tessellation `τ_0`.
  - *Obstruction.* This is sharp quad-diagonal exclusivity. An invariant mean makes both
    diagonals of a quad equal in mean, through five monotone nested moves, while exactly one of
    them is present at each point.
  - The test above, which looks for an `H`-invariant probability on a compact space, is
    replaced by the test "does `H` fix a quad-complete lamination?". The new test needs no
    compact space and no spectral estimate.
  - *Still open.* Candidates `H` whose orbits on chord systems contain no quad-complete fixed
    point, for example stabilizers of laminations with non-triangular gaps. Not tested.
