---
rg: 2
id: thompson-t-identities-hold-on-linearized-blow-ups
kind: claim
title: Every group of orientation-preserving homeomorphisms of a Denjoy blow-up of the circle along T-orbits, rational or irrational, that contains T acting on the gaps by one-sided derivatives satisfies all mixed identities of T
distinct_from:
  circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities: that proves part (F) for irrational orbits, with T affine on the gaps and M the maps over T; this allows rational orbits, where stabilizers have nontrivial germs, and any M inside Homeo+ of the blow-up, by mirroring gap points at scale ε next to the collapsed point.
  thompson-t-identities-one-word-basis-over-cantor-overgroups: that uses one word to force orientation in overgroups where T acts in the standard way; this handles overgroups where T acts in a blown-up way, which that proof does not reach.
  fp-simple-group-with-non-finitely-based-mixed-identities: that lists rational-orbit blow-ups among the surviving candidate witnesses at T; this kills them when the gap action is the derivative action.
---

**ESTABLISHED** by the proof below. Lane proof by bh-ffwz-q59, 2026-09-18. It is elementary and
not reviewed, and no priority is claimed.

## Setting

- **The blow-up.** `T` acts on `S^1 = R/Z` in the standard way. Let `Q ⊂ S^1` be a union of
  `T`-orbits, rational or irrational. Form the circle `C_Q` by replacing each `q ∈ Q` with a
  closed interval `Ī_q`, the lengths being summable, and let `π : C_Q → S^1` collapse each
  `Ī_q` to `q`.
- **Gap coordinates.** Give the interior `I_q` of each gap a coordinate `s ∈ R`, with `s < 0`
  on the left side of `q` and `s > 0` on the right.
- **The derivative action.** `t ∈ T` acts on `C_Q` as `t` off the gaps. It maps `I_q` to
  `I_{tq}` by `s ↦ t'_−(q) s` for `s < 0` and `s ↦ t'_+(q) s` for `s > 0`, using the one-sided
  slopes of the piecewise-linear map `t`.
  - This is an action, by the chain rule for one-sided slopes.
  - Each `t` is a monotone bijection of `C_Q`, hence an orientation-preserving homeomorphism.
  - The action is faithful. Write `T_Q` for its image.
- **Rational orbits.** At rational points the stabilizer `T_q` has nontrivial germs, and it
  acts on `I_q` by the corresponding scalings.
- **Irrational orbits.** There stabilizer germs are trivial: an affine map with dyadic data
  and slope `≠ 1` fixes only rational points. The gaps are then permuted by scalings only.

## Statement

For every `k ≥ 1` and every `M` with `T_Q ≤ M ≤ Homeo+(C_Q)`,
`J_k(M; T) = J_k(T)`, identifying `T` with `T_Q`.

## Proof

`J_k(M; T) ⊆ J_k(T)` because `T ≤ M`. For the converse, let `u ∈ T * F_k` and `x ∈ M^k` with
`u(x) ≠ 1`. We produce `x' ∈ Homeo+(S^1)^k` with `u(x') ≠ 1`. Part (C) of
`circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities` then gives `u ∉ J_k(T)`.

1. **A trajectory avoiding gap endpoints.**
   - Write `u = ℓ_L ⋯ ℓ_1` in letters: constants `c ∈ T` or `x_m^{±1}`.
   - The support of `u(x)` is open and uncountable. Only countably many points have some
     partial trajectory `p_j = ℓ_j(p_{j−1})` hitting a gap endpoint.
   - So choose `p_0` with `p_L ≠ p_0` and every `p_j` either off `⋃ Ī_q` or inside some open
     `I_q`.
2. **The mirror map.** For `ε > 0` define `μ` on the finite set `P = {p_j}`:
   - `μ(p) = π(p)` off the gaps;
   - `μ(s) = q + εs` for `s ∈ I_q`.
3. **Choice of ε.** Take `ε` so small that:
   - `μ` is injective on `P` and preserves the cyclic order of `P`;
   - for every constant step `p_j = c(p_{j−1})` with `p_{j−1} = s ∈ I_q`, the map `c` is linear
     on the side of `q` containing `q + εs`, between `q` and `q + εs`.

   Both are finitely many open conditions. Distinct collapsed points are distinct, and points of
   one gap are ordered by `s`. Each constant is piecewise-linear with finitely many breakpoints.
4. **Constant steps commute with μ.**
   - Off the gaps, `μ(c p) = c π(p) = c μ(p)`.
   - On a gap, `c(q + εs) = c(q) + ε c'_±(q) s = μ(c(s))`.
5. **Variable steps.**
   - For each `m`, the pairs `(μ(p_{j−1}), μ(p_j))` with `ℓ_j = x_m`, and the reversed pairs
     with `ℓ_j = x_m^{−1}`, form a well-defined partial injection of `S^1`, because `x_m` is a
     bijection.
   - It preserves the cyclic order, because `x_m` and `μ` do.
   - A finite partial injection of `S^1` that preserves the cyclic order extends to some
     `x'_m ∈ Homeo+(S^1)`, by piecewise-linear interpolation.
6. **Conclusion.** By steps 4 and 5, `u(x')` maps `μ(p_0)` to `μ(p_L) ≠ μ(p_0)`. ∎

## What this closes and what it leaves

- **Closes.** The rational-orbit blow-ups that Attempt 5 of
  `fp-simple-group-with-non-finitely-based-mixed-identities` left alive, in their natural form
  where `T` acts on gaps by derivatives. It also extends part (F) there from the maps over `T`
  to every `M ≤ Homeo+(C_Q)`.
- **Leaves.**
  - Blow-ups where `T_q` acts on `I_q` by something other than its germ scaling. Examples are the
    trivial action at a rational point, or `T_q ≅ F` acting faithfully on `I_q`. There a mirror
    point next to `q` does not exist.
  - Orientation-reversing overgroups of blow-ups.
  - Abstract overgroups.

## Lesson for general BH

For circle-type hosts, the mixed identities are visible at every scale, including infinitesimal
ones. A blow-up gap in which the host acts by its own germs is just a microscope on one point, and
a finite trajectory in the gap can be copied at a small scale next to the point.
- **Consequence for BFFHZ Question 3.2 at T.** A witness against a finite basis can only come from
  gap actions that are not germ actions, or from purely algebraic `T`-groups. Every geometric
  model that is faithful to the germs is dead.
