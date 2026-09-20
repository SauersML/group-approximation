---
rg: 2
id: fpbs-heavy-pair-is-automatic-via-one-loxodromic
kind: claim
title: Every nonzero nonatomic sigma-finite Gamma-invariant boundary measure of every nonelementary hyperbolic group has pieces A1, A2, built from nested pieces of the fundamental annuli of a single loxodromic, with infinite square return sum and a.e. finite returns; so (heavy-pair) holds for F_2, where no square is conservative, and heavy elements with a common attracting point produce no atom
distinct_from:
  fpbs-invariant-boundary-squares-need-heavy-returns: that proves the heavy-return condition is necessary for a conservative square and names (heavy-pair) and the attracting-point test as the next step. This shows (heavy-pair) is satisfied by every nonatomic invariant measure of every nonelementary hyperbolic group, including F_2, so it is not a test, and it refutes the attracting-point route to an atom.
  fpbs-rotation-boundary-class-refutes-shadow-summability: that gives divergent shadow sums in a quasi-invariant rotation class with dissipative diagonal. This works for every invariant measure, with the divergence coming from one cyclic subgroup, and for the self-return quantities a_g, b_g rather than for shadow masses.
  fpbs-finite-fibre-bb-classes-are-boundary-squares: that reduces the finite-fibre Bevilacqua--Bowen half to (II_inf-square) and proves for cost > 1 groups that no square is conservative; here that non-existence result is used to calibrate (heavy-pair).
---

**ESTABLISHED (written proof: `research/fpbs-heavy-pair-is-automatic-via-one-loxodromic-proof.md`).** This is a
calibration. It settles the named statement (heavy-pair) of
`fpbs-invariant-boundary-squares-need-heavy-returns` with the answer yes, for every nonelementary hyperbolic group, and
for a reason that has nothing to do with conservativity. (II_inf-square) stays OPEN.

**Why this matters for the flagship.** For a cocompact `Gamma < Sp(n,1)`, the finite-fibre half of the
Bevilacqua--Bowen route to fixed price one is equivalent to (II_inf-square). The only named next step toward a
negative answer was (heavy-pair), and the proposed way to kill it was: the attracting points of the heavy elements
must converge, which would give an atom. Both are dead for every nonelementary hyperbolic group, so they cannot tell
`Sp(n,1)` lattices apart from `F_2`.

## Setting

As in `fpbs-invariant-boundary-squares-need-heavy-returns`:
- `Gamma` is nonelementary hyperbolic, and `lambda` is a nonzero, nonatomic, sigma-finite, `Gamma`-invariant Borel
  measure on `dGamma`. Ergodicity is not needed.
- `R(E) = sum_{g in Gamma} (lambda x lambda)(E cap g^{-1} E)`.
- `a_g`, `b_g`, `a'_g`, `b'_g` are the self-return masses of Theorem 2 there.

## Results

**Lemma A (open sets are infinite).** `lambda(U) = infinity` for every nonempty open `U` in `dGamma`.

**Theorem B (one loxodromic gives an infinite return sum).** Let `h` be loxodromic, with fixed points `h^+` and
`h^-`. Then there are Borel sets `A1`, `A2` of finite positive measure and disjoint closures, with `A1` near `h^+` and
`A2` near `h^-`, and a power `f = h^N`, such that:
1. `(lambda x lambda)(E cap f^k E) = T_k^2` for `E = A1 x A2` and all `k >= 1`, where
   `T_k = sum_{i >= k} (i+1)^{-3/2} >= 2 (k+1)^{-1/2}`. So `R(E) >= sum_k T_k^2 = infinity`.
2. Every point of `E`, apart from the null set of pairs involving `h^+` or `h^-`, satisfies `f^k(xi,eta) in E` for
   only finitely many `k in Z`. So the whole divergence in item 1 comes from a subgroup that acts dissipatively on `E`.

**Corollary C ((heavy-pair) is automatic).** For the `D`, `n_0` of Lemma 1 of
`fpbs-invariant-boundary-squares-need-heavy-returns` applied to `K1 = cl A1` and `K2 = cl A2`,
`sum_g a_g b_g + sum_g a'_g b'_g = infinity`. So (heavy-pair) holds for the ordered pair `(A1, A2)` or for
`(A2, A1)`. Such measures exist for every nonelementary hyperbolic group, by Proposition 5 of
`fpbs-finite-fibre-bb-classes-are-boundary-squares`, including ergodic ones. So:
1. **(heavy-pair) is true for every nonelementary hyperbolic group**, including `F_2` and surface groups. By
   Corollary 6.2 there, those groups have no invariant measure with a conservative square. So (heavy-pair) does not
   imply (II_inf-square), and no proof that (heavy-pair) fails can exist for any hyperbolic group.
2. **The attracting-point test is refuted.** The heavy elements `f^{-k}` of Theorem B all have the same attracting
   point `h^-`. So their attracting points converge, yet `lambda` has no atom. The atom argument (Corollary 4.2 of
   the w19 node) needs contracted masses bounded below, and here they are `T_k -> 0`.

## Class killed

Killed: every attempt to decide (II_inf-square) negatively by showing that an integrated return count over a product
of pieces is finite, or that heavy self-returns cannot line up. This covers:
- `R(A1 x A2) < infinity`;
- (heavy-pair);
- the sphere sums and sphere maxima of `a_g`, `b_g`;
- convergence of attracting points along heavy sequences.

For every invariant `lambda`, some product of pieces fails all of these tests, and the failure comes entirely from one
cyclic subgroup, which returns only finitely often at each point.

- **Invariant it misses.** The pointwise return count `N(x) = #{g : g x in E}`. We have `R(E) = ∫_E N`, and `N` can
  be finite a.e. yet not integrable on a set of finite measure.
- **Where it dies.** The step from `R(E) = infinity` to "a.e. infinitely many returns". This inference is false for
  infinite invariant measures, and fails already for `<h>` acting on nested annulus pieces.

## What this leaves

A negative answer to (II_inf-square) for `Sp(n,1)` lattices has to be pointwise. For `E = A1 x A2` and a.e.
`(xi,eta)` in `E`, the return set lies in a `C`-neighbourhood of the geodesic from `eta` to `xi`. Conservativity asks
whether a.e. such geodesic meets infinitely many translates of the returning configuration. That is a recurrence
question for the geodesic flow over `Gamma`, with the flow measure of `lambda x lambda`, which is infinite on every
open set. Any count that can succeed has to be truncated to sets `{N <= L}`, where finite returns do give finite
sums, or has to remove the contribution of every elementary subgroup. It cannot be a plain return sum over product
pieces.
