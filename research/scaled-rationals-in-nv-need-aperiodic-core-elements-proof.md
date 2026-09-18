---
rg: 2
id: scaled-rationals-in-nv-need-aperiodic-core-elements-proof
kind: route
title: A scaling by p/q gives f d^q f^-1 = d^p for every d, and the odometer base has a fixed point of exponent (1,0)
target: scaled-rationals-in-nv-need-aperiodic-core-elements
requires:
  - bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
  - bs12-images-in-nv-have-logarithmic-table-length
  - rationals-embed-in-brin-thompson-group-2v
---

**Item 1.** Identify `D` with `(Q,+)`, so that `f x f^-1 = a x` for `x ∈ D`.
Write `a = p/q` in lowest terms, with `p, q != 0`. Then `a != ±1` means
`|p| != |q|`.
- For `d ∈ D` (additively `x`), `f (q x) f^-1 = a q x = p x`. Multiplicatively,
  `f d^q f^-1 = d^p`.
- `d` has infinite order when `d != 1`, since `D` is torsion-free.
- `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` applies with
  `g = d`, `k = q`, `l = p`, and gives items 1–3 of its statement. Item 3 there
  gives a nonempty aperiodic core, because `d` has infinite order.
- If `a = p ∈ Z` (`q = 1`), then `f d f^-1 = d^p` with `|p| >= 2`, and
  `bs12-images-in-nv-have-logarithmic-table-length` gives `L(d^N) <= c (1 + log_2 |N|)`.

**Item 2.**
- **The fixed point.** In the odometer copy, `s_0 = t × id` with `t(00w) = 0w`,
  `t(01w) = 10w`, `t(1w) = 11w`. The brick `1C × C` has table image
  `11C × C`. So `(1^∞, y)` is a fixed point of `s_0` for every `y`, with
  exponent vector `δ_(s_0) = (|11| − |1|, 0) = (1, 0) != 0`.
- **In nV.** Under `2V <= nV`, `g ↦ g × id`, the exponent vector gains zero
  entries and stays nonzero.
- **Conclusion.** If `f` scaled `R` by `a != ±1`, item 1 would force every
  periodic exponent of `s_0 ∈ R` to vanish. That is a contradiction.
- **Other copies.** The same argument applies to any copy of `Q` containing an
  element with a periodic point of nonzero exponent. The register copies built on
  `g × id` (item 1 of `twisted-bt-point-fixing-actor-elements-are-divisible`,
  with `G` trivial) contain `g × id`. So they are covered whenever `g ∈ V` has a
  periodic point of nonzero exponent.
- **Kojima--Sheng's copies.** Whether this holds for their horizontal-slide base
  was not checked. All their continuum many copies share one infinite cyclic
  subgroup, so one check would decide all of them. ∎
