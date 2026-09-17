---
rg: 2
id: fpbs-locally-free-free-action-costs-are-c-star-or-infinite-proof
kind: route
title: Squeeze free-action cost between the Gaboriau bound 1 + beta_1 = c* and the minimal-rank exhaustion bound on pseudocost
target: fpbs-locally-free-free-action-costs-are-c-star-or-infinite
requires:
  - locally-free-groups-first-l2-betti-equals-c-star-minus-one
  - fpbs-amen2-betti-cost-input
  - tucker-drob-pseudocost-exhaustion-bounds
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Direct proof (artifact §5). Let `a` be a free p.m.p. action of `Γ`. Let
`Δ_0 ≤ Δ_1 ≤ ⋯` be finitely generated subgroups with union `Γ` and
`rk Δ_n ≤ c*`; the minimal-rank exhaustion of the Theorem L proof has this
property.

1. **Upper bound on pseudocost.** The `rk Δ_n` generators of `Δ_n` form a
   graphing of `E_{a|Δ_n}` of cost `rk Δ_n`. The relations `E_{a|Δ_n}` are
   increasing with union `E_a`. By the definition in
   `tucker-drob-pseudocost-exhaustion-bounds`,
   `PC(a) ≤ liminf C(E_{a|Δ_n}) ≤ c*`.
2. **Lower bound on cost.** By `fpbs-amen2-betti-cost-input`,
   `C(a) ≥ 1 + beta_1^(2)(Γ)`. By
   `locally-free-groups-first-l2-betti-equals-c-star-minus-one`, this is `c*`.
3. **Dichotomy.** If `C(a) < ∞`, item (1) of
   `tucker-drob-pseudocost-exhaustion-bounds` gives
   `C(a) = PC(a) ≤ c* ≤ C(a)`. Otherwise `C(a) = ∞`. If `c* = ∞`, step 2
   already gives `C(a) = ∞`.
4. **Exact pseudocost.** If some free action has finite cost, step 3 gives
   `C(Γ) = c* < ∞`. Item (4) of `tucker-drob-pseudocost-exhaustion-bounds`
   gives `PC(b) ≥ c*` for every free `b`. With step 1, `PC(b) = c*`.
5. **Consequences.** The set of free costs lies in `{c*, ∞}`, so fixed price
   fails iff both values occur. A group without fixed price then has
   `C(Γ) = c* < ∞` and a free `b` with `PC(b) = c* < ∞ = C(b)`. That is shape
   (B) of the passage artifact's Theorem G and a free-action instance of
   Tucker-Drob Q 7.6. Condition (L), `c* ≤ C(Γ)`, is step 2.
