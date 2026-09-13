---
rg: 2
id: rigid-two-patch-seed-never-injective-proof
kind: route
title: Two-site relation moves on nonamenable placements, a fourth move under (a^-1 b)^2 = 1, and the Garden of Eden theorem with measure preservation on amenable ones
target: rigid-two-patch-seed-rule-is-never-injective
requires:
  - amenable-groups-satisfy-the-garden-of-eden-theorem
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - research/artifacts/rigid-two-patch-seed-relation-moves-2026-09-12.md
  - research/artifacts/w7-vf-nonlinear-verification-2026-09-12.md
---

Artifact Sections 1–4.

1. **Reduction to `H = <a, b>`.** A collision over `H` extends to `G` coset by coset.
2. **Amenable `H`.**
   - An injective automaton is pre-injective, so it is surjective by the Garden of Eden theorem, and
     then bijective.
   - A bijective automaton preserves the uniform Bernoulli measure, so `mu_3` would be balanced. Its
     counts are `8, 9, 10`.
3. **Nonamenable `H`.** Put `c = a^-1 b`.
   - **Three moves.** `T_ab`, `T_1a` and `T_1b` (Section 1) each realize unless one of their conflict
     relators (Section 2) holds in `H`. Every relator other than `c^2`, `c^3`, `a^2`, `a^3`, `b^2` and
     `b^3` breaks distinctness, or makes `<a, b | r>` cyclic, `Z^2` or the Klein bottle group.
   - **`c^2 = 1`.** Move `C` (Section 3) realizes. Its conflicts force `a = 1`, `c = 1` or `b = 1`.
   - **Otherwise.** `c^3 = a^k = b^m = 1` with `k, m` in `{2, 3}`, so `H` is a quotient of the von Dyck
     group `<x, y | x^k, y^m, (xy)^3>` with `x = a^-1` and `y = b`. That group has order 6 or 12, or is
     the Euclidean `(3,3,3)` group. All are amenable, a contradiction.
   - **Collisions.** In each realized move the window table shows equal outputs at every touched
     window, and the untouched windows read identical configurations.

**Verification (w7-vf-nonlinear, 2026-09-12): valid.**
- **Tables.** Every window table of Sections 1 and 3 was recomputed by hand.
- **Coincidences.** All 55 pairs of each two-site move were enumerated. The conflicting pairs number 34,
  39 and 40, and their relators match the Section 2 lists exactly.
- **Move `C`.** Its 17 conflicting pairs force `a = 1`, `c = 1` or `b = 1`.
- **Classification.** The relator classification and the von Dyck orders were checked, and the case split
  over `H` is exhaustive.

Details are in `research/artifacts/w7-vf-nonlinear-verification-2026-09-12.md`, Section 1.
