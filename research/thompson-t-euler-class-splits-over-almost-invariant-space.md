---
rg: 2
id: thompson-t-euler-class-splits-over-almost-invariant-space
kind: claim
title: "There is a nonsingular Thompson T-space whose Koopman representation has almost invariant vectors and over which the Euler extension T-bar splits measurably (a real cocycle beta on T-bar with beta(z,.) = 1)"
distinct_from:
  lifted-thompson-t-is-a-t-menable: that is the Haagerup property of T-bar; this is a measure-theoretic statement about T that implies it through central-extension-haagerup-from-measurable-euler-splitting, and is not known to follow from it
  lifted-thompson-t-center-has-relative-t: that is the refuting statement for T-bar; this claim implies its negation, but its own failure refutes nothing
  thompson-t-orbits-carry-no-invariant-means: that kills counting measure on orbits in S^1; this asks for spaces that do not map to S^1 at all
artifacts: []
---

**Statement (MT).** There are:
- a standard σ-finite measure space `(X, μ)` with a nonsingular action of Thompson's `T`,
  whose Koopman representation `κ` has almost invariant unit vectors;
- a measurable `β : T̄ × X → R`, with `T̄` acting through `T`, satisfying the cocycle identity
  and `β(z, ·) = 1` a.e.

**Status.** OPEN.

## Role

- (MT) implies `lifted-thompson-t-is-a-t-menable`, by
  `central-extension-haagerup-from-measurable-euler-splitting`. `T` is Haagerup by Farley,
  `thompson-v-has-haagerup-property`. The route is
  `lifted-thompson-t-a-t-menable-via-measurable-euler-splitting`.
- The failure of (MT) does not refute the target. Only a converse would make it necessary, and
  that converse is not established (see Remarks).

## Forced shape (established)

By `perfect-extension-splittings-are-not-uniformly-integrable`, for any witness `(X, μ, β)`:
- (F1) No subsequence of the almost invariant densities `ν_n = ξ_n² μ` makes all `β(g, ·)`
  uniformly integrable. In particular, `β` is not bounded, and if `μ` is an invariant
  probability then `β` is not in `L¹`.
- (F2) `X` admits no measurable `T`-equivariant map to `S^1`. Otherwise the bounded circle
  splitting pulls back, and Part 3 of that claim gives spectral gap.

So the circle, its orbits, and every space fibred over it are excluded. The Cantor set
`{0,1}^N`, with `T ≤ V` acting and the binary coding map onto `S^1` being equivariant, is
excluded too.

## Remarks (not established)

- *Converse, sketch only.* Suppose `T̄` has a cnd function `ψ` with `Σ_m e^{-ψ(z^m)/8} < ∞`. Then
  the nonsingular Gaussian action built from the affine action of `ψ` should make `z`
  dissipative. Its quotient by `⟨z⟩` should be a witness for (MT), with almost invariant
  vectors pushed down by fibrewise `ℓ²` norms.
  - The dissipativity criterion for nonsingular Gaussian actions, in the style of
    Arano–Isono–Marrakchi, was not read verbatim.
  - Boosting the growth of an arbitrary proper `ψ` on `⟨z⟩` failed. Spectral reweighting by
    `w(ρ(z))` needs a spectral-measure comparison that was not proved.
- The discrete special case is `thompson-t-co-amenable-subgroup-kills-real-euler-class`.

## Attempts

- 2026-09-18 (swarm-0917-w9-w9-nv-follow): statement isolated; forced shape (F1) and (F2)
  proved; discrete special case split off. Not decided.
