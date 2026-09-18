---
rg: 2
id: ct-p-z-isomorphism-type-remembers-the-number-of-primes
kind: claim
title: If CT_P(Z) and CT_Q(Z) are isomorphic for finite sets P, Q of odd primes then |P| = |Q|; this answers Kourovka Problem 17.60 for sets of different sizes
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
artifacts:
  - research/artifacts/gq-bh-bh-kourovka-problems.md
---

**ESTABLISHED** (lane proof, not reviewed). It uses the parent node plus Matui
1210.5800, Theorem `iso2`, read at source. No priority is claimed.

Kourovka 17.60 (S. Kohl) asks whether the groups `CT_P(Z)` are pairwise
nonisomorphic. This node settles the case `|P| ≠ |Q|`. The case `|P| = |Q|` with
`P ≠ Q` stays OPEN; a candidate invariant is sketched below.

## Statement

For finite sets `P, Q` of odd primes, `CT_P(Z) ≅ CT_Q(Z)` implies `|P| = |Q|`.

## Proof

1. **Reduce to groupoids.** By the parent node, `CT_P(Z) = [[G_{Λ_P}]]`, and
   `G_{Λ_P}` is essentially principal, étale and minimal, with Cantor unit space.
   Matui's Theorem `iso2` ((2) ⇔ (1)) gives: `[[G_1]] ≅ [[G_2]]` as discrete groups
   iff `G_1 ≅ G_2` as étale groupoids. So an isomorphism `CT_P(Z) ≅ CT_Q(Z)` yields
   `G_{Λ_P} ≅ G_{Λ_Q}`, and groupoid isomorphisms carry isotropy groups to isotropy
   groups.
2. **Every isotropy group sits in `Z^k`.** An element of the k-graph groupoid is a
   triple `(x, n, y)` with `n ∈ Z^k` (`k = |P| + 1`). An isotropy element at `x` is
   `(x, n, x)`, determined by `n`. So `G_x^x` embeds in `Z^k`, and every isotropy
   group has rank at most `k`.
3. **The bound is attained at 0.**
   - For `m, m' ∈ N_{P'}`, the basic bisection `Z((m, 0), (m', 0))` acts as
     `x ↦ (m/m') x` on the box `B(0, m')`, fixes `0`, and has
     `n = d(m) − d(m')`.
   - Every `n ∈ Z^k` arises this way, so `G_0^0 ≅ Z^k`.
4. **Conclusion.** The maximal rank of an isotropy group, `|P| + 1`, is an isomorphism
   invariant of `G_{Λ_P}`, hence of `CT_P(Z)`.

## Toward the equal-size case (sketch, not a proof)

This candidate invariant recovers the set of primes `P` itself, not just its size.

1. **Coordinate directions.** At `x = 0`, for `q ∈ P'`, the germ of `×q` contracts the
   `Z_q` coordinate and acts isometrically, by a unit, on the other coordinates.
   The stable set of this germ is `{0} × Z_q` (the other coordinates vanish).
2. **Quotient by the contraction.** Pass to the quotient of the stable set by `×q`,
   i.e. `Z_q^×`. The commuting germs `×p` (`p ≠ q`) act on it by multiplication. The
   result is an equicontinuous minimal system with continuous eigenvalues of all
   `q`-power orders.
3. **Recovering `P`.** One could then read off `P'` as the set of primes `q` for
   which some rank-one direction of a full-rank isotropy group has this property.

Making "stable set of a germ" and the induced system intrinsic to the groupoid,
invariant up to finite index and independent of the base point, is the open step.
