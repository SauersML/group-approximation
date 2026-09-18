---
rg: 2
id: hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank
kind: claim
title: For every n >= 4 there is a one-ended hyperbolic F_n-by-Z group with a Pisot stretch factor that contains a genus-two surface group, all certified by one legal f-folded fatgraph
distinct_from:
  hyperbolic-f3-by-z-family-with-genus-two-surfaces: that stays in rank 3; this adds a chain of new letters and reaches every fibre rank n >= 4. Each group here has first Betti number 1, so its fibre rank is an isomorphism invariant.
  hyperbolic-f3-by-z-with-genus-two-surface-certificates: that certifies two automorphisms of F_3; this reuses one of its pairings unchanged in every rank and proves hyperbolicity for all ranks at once, with no per-rank computation.
  legal-f-folded-fatgraphs-give-surface-subgroups: that is the rank-free criterion; this supplies hyperbolic instances in every rank.
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for all one-ended hyperbolic groups; this covers one explicit hyperbolic free-by-cyclic group in each fibre rank.
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/pisot_chain_family.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/pisot_chain_family_k40.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_rankn.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi1028.json
---

**ESTABLISHED.** Every `k` is handled at once: the hyperbolicity argument is by hand, and the
surface argument uses a single fixed 16-dart certificate that is already verified by computer.
Proof in `hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank-proof`.

For `k >= 1`, let `F = F(a, b, c, d_1, ..., d_k)` have rank `n = k + 3`, and define

```text
phi_k : a -> a^7 c^9 d_1 b,   b -> ca,   c -> babb,   d_i -> d_{i+1} (1 <= i < k),   d_k -> b.
```

1. For every `k >= 1`:
   - `phi_k` is a positive automorphism with a primitive transition matrix `M_k`;
   - its characteristic polynomial is
     ```text
     chi_k(t) = t^k (t^3 - 7t^2 - 13t - 7) - (t + 1);
     ```
   - `chi_k` has exactly one root outside the closed unit disk and none on the unit circle, so the
     stretch factor is a Pisot unit.
2. For every `k >= 1`, `chi_{M_k^j}` is irreducible over `Q` for all `j >= 1`. So `phi_k` is fully
   irreducible and atoroidal, and `G_k = F x|_{phi_k} Z` is a one-ended hyperbolic group.
3. For every `k >= 1`, the pairing of `surface_phi1028.json` (with `partial^- = {bc, BC}`) is a legal
   `f_k`-folded fatgraph with `chi = -2`. So `G_k` contains the fundamental group of the closed
   orientable surface of genus 2.
4. `H_1(G_k) = Z ⊕ T` with `|T| = |chi_k(1)| = 28`. Since `b_1(G_k) = 1`, the fibre rank `n` is an
   isomorphism invariant. Hence the groups `G_k` are pairwise non-isomorphic, and none of them has
   fibre rank 3.

Together with `hyperbolic-f3-by-z-family-with-genus-two-surfaces`, main has, for every `n >= 3`, a
one-ended hyperbolic `F_n x| Z` that contains a genus-2 surface group.

## Why every rank works at once

- **The certificate ignores the new letters.** It reads only:
  - `phi(b)` and `phi(c)`;
  - the gates of the six directions `a, b, c, A, B, C`.

  `Df` maps these six directions among themselves in the same way as for
  `phi_1 = (a -> abb, b -> ca, c -> babb)`. This holds whenever `phi(a)` starts with `a` and ends
  with `b`.
- **The characteristic polynomial splits into a fixed part and a chain part.**
  - The `a, b, c` block gives `A(t) = t^3 - 7t^2 - 13t - 7`.
  - The chain `d_1 -> ... -> d_k -> b` contributes `t^k` and the cofactor `t + 1`.
  - `A` is a Pisot polynomial: one root in `(8, 9)`, and a complex pair of modulus `< 1`.
  - On `|t| = 1` we have `|A(t)| > |t + 1|`, exactly. By Rouché, each `chi_k` keeps exactly one
    root outside the disk.
- **Irreducibility is then automatic.** An integer factor with all roots inside the open unit
  disk would have a nonzero integer constant term of modulus `< 1`.

The exponents 7 and 9 were chosen so that `A` is Pisot and dominates `|t + 1|` on the circle. The
earlier choice `phi(a) = a c d_1 b` gives `A = t^3 - t^2 - 5t - 1`, which has two roots outside
the disk, and there irreducibility is a separate problem in each rank.

## Evidence

- `pisot_chain_family.py`, **part A**, checks by exact sympy computation:
  - `A(8) < 0 < A(9)`;
  - `disc(A) = -5324 < 0`;
  - `|A(e^{is})|^2 - |1 + e^{is}|^2 = -56x^3 + 144x^2 + 390x + 194` with `x = cos s`;
  - this cubic has no root in `[-1, 1]` and is positive there.
- **Part B**, for `k = 1, ..., 40`, runs `verify_surface_rankn.py`. Each run checks:
  - the closed-form inverse, by free reduction;
  - positivity, `|det| = 1` and primitivity;
  - exact irreducibility of `chi_M` over `Z`;
  - the non-palindromic `chi_{M^2}` for even `n`;
  - (L), (2), (3), (4), connectivity and `chi(X) = -2` on the unchanged pairing.

  It also compares `chi_M` with the closed form. Result: 40 of 40 (`pisot_chain_family_k40.log`).
  This double-checks the ranks `4 <= n <= 43`; the proof itself needs no per-rank computation.

## Scope

- The result gives one group per fibre rank. It does not cover all hyperbolic free-by-cyclic
  groups, not even in rank 3. Automorphisms where the power-one criterion is silent (see
  `legal-folded-certificates-at-power-one-census`) are untouched.
- The certificates use power 1 and genus 2 only.

**Literature scope.** Brady and coauthors (second-hand only) report hyperbolic free-by-cyclic
groups with surface subgroups. No source was checked for examples in each fibre rank. So the
novelty claim is about the route and the explicit family, not about existence.
