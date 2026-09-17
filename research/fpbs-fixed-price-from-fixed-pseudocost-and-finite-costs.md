---
rg: 2
id: fpbs-fixed-price-from-fixed-pseudocost-and-finite-costs
kind: route
title: Fixed pseudocost plus finiteness of all free costs at groups of finite cost gives fixed price, bypassing the countable passage
target: fpbs-fixed-price-universal
requires:
  - fpbs-countable-groups-have-fixed-pseudocost
  - fpbs-finite-cost-groups-free-actions-have-finite-cost
  - tucker-drob-pseudocost-exhaustion-bounds
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
  - research/artifacts/fpbs/docs/fixed-price-countable-passage.md
---

Direct proof (artifact Theorem 4.1). Let `Γ` be countably infinite and `b` a
free p.m.p. action, with `C(Γ) = inf { C(a) : a free }`.

- **Case `C(Γ) = ∞`.** Every free action has cost `∞`, so `C(b) = C(Γ)`.
- **Case `C(Γ) < ∞`.** Fix `ε > 0` and a free `a` with `C(a) < C(Γ) + ε`.
  1. Item (1) of `tucker-drob-pseudocost-exhaustion-bounds` gives
     `PC(a) = C(a)`.
  2. `fpbs-countable-groups-have-fixed-pseudocost` gives
     `PC(b) = PC(a) < C(Γ) + ε`. As `ε` is arbitrary, `PC(b) ≤ C(Γ)`.
  3. Item (4) of `tucker-drob-pseudocost-exhaustion-bounds` gives
     `PC(b) ≥ C(Γ)`.
  4. `fpbs-finite-cost-groups-free-actions-have-finite-cost` gives
     `C(b) < ∞`. Item (1) then gives `C(b) = PC(b) = C(Γ)`.

So all free actions of `Γ` have cost `C(Γ)`.

**Remarks.**
- The route uses no hypothesis on finitely generated groups and does not pass
  through `fpbs-fixed-price-countable-from-finitely-generated`.
- The first prerequisite is fed by the finitely generated statement
  `fpbs-relative-sandwich-cost-bernoulli-lower-bound`.
- Conversely, the flagship implies the second prerequisite, and it implies the
  first at every group with `C(Γ) < ∞`.
- The two prerequisites fail independently:
  - fixed pseudocost alone still allows shape (B), an infinite free cost at a
    group of finite cost;
  - finite costs alone still allow shape (A), no fixed pseudocost.
