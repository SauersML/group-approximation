---
rg: 2
id: hyperfinite-coefficient-graphing-proof
kind: route
title: Count injective columns on finite classes of an exhaustion and transport the mass
target: hyperfinite-coefficient-graphing-excludes-corner-witnesses
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
  - odd-measure-space-has-no-honest-thompson-compression
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Proposition 5.1, Theorem 5.3 and Corollary 5.4 of the artifact.

**Expansion.** In the orbit module, `(xi_1, xi_2) -> sigma_1 xi_1 + sigma_2 xi_2` maps `l(J)^2` into the
functions on the column points, and `tau_i` recovers `xi_i`. Case 2 uses `c'` as the left inverse, and
`q_[0]` confines the image to `U_[0]`.

**Exhaustion.**
- *Small boundary.* If `R_Gamma` is the union of increasing finite Borel subrelations `R_n`, the boundary
  set `∂_n` of points with a neighbour outside their `R_n`-class has `lambda(∂_n) -> 0`, because degree is
  bounded.
- *Counting.* On each class `C`, the interior `C° = C \ ∂_n` satisfies `2|C°| <= |C|` in case 1, or
  `|C°| <= |C ∩ U_[0]|` in case 2.
- *Transport.* Mass transport on the finite relation `R_n` gives `lambda(M_- \ ∂_n) <= 1/2`, using
  `lambda(U_[0]) = 1/2` in case 2. This is a contradiction once `lambda(∂_n) < 1/2`.

**Degree two.**
- *Case 1.* Components are finite, rays, or lines. A finite component `K` gives `2|K| <= |K|`, and a segment
  of `m >= 3` points has at most `m + 2 < 2m` column points.
- *Case 2.* Finite components lie in `U_[0]`, and each infinite component meets `U_[1]` in at most two
  points. A Borel set meeting every infinite class finitely is null by mass transport, but
  `lambda(U_[1]) = 1/2`.
