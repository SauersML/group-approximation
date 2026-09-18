---
rg: 2
id: f-dyadic-endpoint-switch-walk-gaps-are-inverse-square
kind: claim
title: The switch-walk-switch spectral gap of F on the dyadics at the root 2^-m is at most a constant over m squared, and F is amenable exactly when it beats that bound by more than a constant factor
distinct_from:
  f-dyadic-ea-iff-inverted-orbit-confinement: that is the qualitative equivalence of extensive amenability with a zero return-probability rate at one fixed root; this compares the gaps at the roots 2^-m, proves the unconditional m^-2 upper bound, and turns the zero-versus-positive question into a constant-factor question at depth m.
  thompson-f-dyadic-ea-witnesses-need-tower-size: that bounds the size of finite extensive-amenability witnesses from Moore's Følner bound; this is a spectral statement about how the gap depends on the root and uses no Følner input.
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open rare-event confinement target; this does not decide it, but gives it an equivalent normalized form at the roots 2^-m.
---

**ESTABLISHED** by `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square-proof` (direct proof; not independently
reviewed; no priority claimed).

**Setting.**
- `D` is the set of dyadic rationals in `(0,1)`, and `F = ⟨x_0, x_1⟩` acts on it in the standard way.
- `μ` is uniform on `S = {e, x_0^{±1}, x_1^{±1}}`.
- `L = (Z/2)^{(D)} ⋊ F` acts on the finite subsets `P_f(D)` by `(φ, g)·A = φ Δ gA`.
- For a root `y ∈ D`, let `δ_y ∈ L` switch the lamp at `y`, let `λ_y` be uniform on `{e, δ_y}`, and put
  `ν_y = λ_y ∗ μ ∗ λ_y` (the switch-walk-switch measure).
- `P_y` is the self-adjoint Markov operator of `ν_y` on `ℓ²(P_f(D))`.
- The gap is `gap(y) = 1 − sup spec P_y`. Write `κ(m) = gap(2^{−m})`, so `κ(1) = gap(1/2)`.

**Theorem.**
1. *Unconditional endpoint bound.* `κ(m) ≤ π²/(5m²)` for every `m ≥ 4`.
2. *Root comparison.* For all `m ≥ 2`, `κ(1) ≤ 20(4m−1)² κ(m)` and `κ(m) ≤ 20(4m−1)² κ(1)`.
3. *Equivalence.* The following are equivalent:
   - `F` is amenable;
   - `F ↷ D` is extensively amenable;
   - `gap(y) = 0` for some (equivalently every) `y ∈ D`;
   - `liminf_{m→∞} m² κ(m) = 0`.
4. *Nonamenable normal form.* `F` is nonamenable exactly when there is `c > 0` with
   `c/m² ≤ κ(m) ≤ π²/(5m²)` for all `m ≥ 4`. The admissible constant is `c = κ(1)/320`.

**Reading.**
- Near the endpoint `0`, both generators act linearly (`x_0` halves and `x_1` is the identity on `[0,1/2]`). A
  switch-walk rooted at `2^{−m}` can keep its whole inverted orbit inside a strip of `m−1` points while its
  slope walk stays in a window of width `m−2`. That "strip strategy" costs only `π²/(5m²)` per step, whatever
  `F` is. This is the source of item 1.
- Transporting the root from `2^{−m}` to `1/2` costs a factor of order `m²` (item 2). So the endpoint gain and
  the transport loss have the same exponent `2`.
- *Consequence.* Amenability of `F` is *exactly* the statement that, at large depth `m`, some strategy beats the
  trivial strip strategy by an unbounded factor (item 3). Nonamenability is exactly the statement that the strip
  strategy is optimal up to a constant, uniformly in `m` (item 4).
- This recasts `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` as a one-constant question at a single
  scale family. It also explains why the endpoint recurrence of `F` gives nothing by itself; see
  `f-ea-endpoint-localization-certificates-stall`.
