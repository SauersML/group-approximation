---
rg: 2
id: metallic-wang-shift-product-is-minimal-with-split-differences
kind: claim
title: The product of the golden and silver metallic mean Wang shifts is a minimal free Z^2 subshift of finite type whose difference sets split into two far parts at every scale
distinct_from:
  labbe-shift-is-wall-rigid: that proves every difference set of one Labbé shift is coarsely connected, because its fault lines cross; this exhibits a different minimal free Z^2 SFT, a product of two shifts with unrelated eigenvalues, whose horizontal faults can be placed independently and far apart, so it is not wall rigid.
  minimal-sfts-have-no-finite-asymptotic-pairs: that shows minimal SFTs have no finite difference sets; this shows that infinite difference sets of a minimal free SFT need not be coarsely connected, which is the remaining refutation route that claim left.
  fp-v-times-subshift-full-groups-force-connected-differences: that is the algebraic necessary condition (coarse connectivity); this is a purely dynamical example that violates it.
artifacts:
  - experiments/metallic-wang-product-2026-09-17/row_fault_check.py
---

**ESTABLISHED (unreviewed).** Proof: `metallic-wang-product-minimality-and-row-faults-proof`.
Uses only results of Labbé, quoted verbatim in the route, and standard facts on torus rotations.

## Setting

- For `n >= 1`, `β_n = (n + sqrt(n^2 + 4))/2` is the `n`-th metallic mean, and `Ω_n ⊆ T_n^(Z^2)`
  is Labbé's metallic mean Wang shift on the tile set `T_n` of `(n + 3)^2` Wang tiles
  (S. Labbé, *Metallic mean Wang tiles II: the dynamics of an aperiodic computer chip*,
  arXiv:2403.03197v3; *I* is [Lab25a] there). `Ω_1` is equivalent to the Ammann 16-tile shift.
- `X = Ω_1 × Ω_2 ⊆ (T_1 × T_2)^(Z^2)`, with the diagonal shift action of `Z^2`. So
  `β_1 = (1 + sqrt 5)/2` and `β_2 = 1 + sqrt 2`.
- `Z^2` carries the generators `±e_1, ±e_2` and the `ℓ^1` metric. For `u, v ∈ X`,
  `Δ(u, v) = {p : u(p) ≠ v(p)}`. A set is `m`-connected if it cannot be split into two nonempty
  parts at distance `> m`. This is the notion of
  `fp-v-times-subshift-full-groups-force-connected-differences`.

## Theorem

1. `X` is a nonempty subshift of finite type on which `Z^2` acts freely and minimally.
2. **Row faults.** For `n >= 1`, `Ω_n` contains `c ≠ c'` with `Δ(c, c') ⊆ Z × {0, 1}`.
   In fact `Z × {1} ⊆ Δ(c, c')`.
3. **Split differences.** For every `m` there are `u, v ∈ X` with `Δ(u, v)` not `m`-connected.
   Explicitly, `Δ(u, v) = Δ_1 ⊔ Δ_2` with `∅ ≠ Δ_1 ⊆ Z × {0, 1}` and
   `∅ ≠ Δ_2 ⊆ Z × {m + 2, m + 3}`.

Part 2 does not by itself break coarse connectivity inside one `Ω_n`. The product is what lets two
faults be moved independently. It stays minimal because the maximal equicontinuous factors are
rotations by `β_1` and `β_2`, and `1, β_1, β_2` are linearly independent over `Q`.

## Consequences

- With `fp-v-times-subshift-full-groups-force-connected-differences`, part 3 makes the full group
  of `G_V × (Z^2 ⋉ X)` not finitely presented. This refutes P2
  (`v-times-golden-silver-wang-product-full-group-is-not-fp`).
- With part 1 of `fp-crossed-products-force-connected-differences`, part 3 means that
  `LC(X, k) ⋊ Z^2` has no finite presentation on the generators `e_a, u_s`, over any field `k`.
  That statement says any presentation on these generators with relators of length `<= n` makes
  every `Δ` `2n`-connected. So `X` is not quantum rigid. This does not refute
  `free-minimal-z2-sft-is-quantum-rigid`, which is existential. It does show that a quantum rigid
  minimal free `Z^2` SFT cannot be a product of two minimal shifts whose faults can be shifted
  independently.
- **Calibration for wall rigidity.** Minimality, freeness, zero entropy, finite type and no finite
  asymptotic pairs together still allow split differences. Coarse connectivity is a strictly
  stronger, genuinely geometric condition.
