---
rg: 2
id: dyadic-tower-subshift-full-group-non-uniform-growth
kind: claim
title: If an infinite minimal subshift has constant towers of height 2^m with bounded induced alphabets at infinitely many scales, its derived topological full group has non-uniform exponential growth
artifacts:
  - research/artifacts/sk-sturmian-growth-plan-2026-09-14.md
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part1.md
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part2.md
distinct_from:
  dyadic-substitution-derived-full-groups-non-uniform-growth: that is the special case of primitive constant-length-2 substitution subshifts, where the towers are ζ^m(X) and the induced system is conjugate to X itself; this isolates the two properties the proof uses, constant dyadic towers and bounded induced alphabets, with no substitution and no recognizability import.
---

**ESTABLISHED (unreviewed; sk-sturmian-growth).**
- **Statement.** Let `(X,T)` be an infinite minimal subshift. Suppose there are `K ≥ 1` and infinitely many `m` with:
  - (H1) a clopen `V_m` with `X = ⊔_(i<2^m) T^i V_m` and `T^(2^m) V_m = V_m`;
  - (H2) a clopen partition `𝒫_m` of `V_m` with `|𝒫_m| ≤ K` whose translates under `S_m = T^(2^m)|V_m` generate the clopen algebra of `V_m`.

  Then `ω([[T]]′) = 1`, and `[[T]]′` has exponential growth, so its growth is non-uniformly exponential.
- **Instance.** Primitive substitutions of constant length 2 with a non-periodic fixed point, with `V_m = ζ^m(X)` and `𝒫_m` the letter cylinders of `(V_m,S_m) ≅ (X,T)`, so `K = |A|`. This gives `dyadic-substitution-derived-full-groups-non-uniform-growth`.
- **Scope firewall.**
  - (H1) forces a continuous eigenvalue `e^(2πi/2^m)`. So no totally minimal subshift satisfies it, and Sturmian subshifts are excluded (see the plan artifact §2).
  - The odometer is not a subshift and fails (H2).

Route: `dyadic-tower-subshift-full-group-non-uniform-growth-proof`.
