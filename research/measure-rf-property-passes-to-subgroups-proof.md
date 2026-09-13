---
rg: 2
id: measure-rf-property-passes-to-subgroups-proof
kind: route
title: Co-induction carries a full-support invariant measure up, and restriction plus the coordinate factor carry residual finiteness back down
target: measure-rf-property-passes-to-subgroups
requires: [rf-actions-induce-from-finite-index-subgroups, extensions-of-aperiodic-sfts-are-not-residually-finite-actions]
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

Artifact part 1, §3, Proposition R.
1. **Subgroups.** Let `H ↷ Y` be Cantor with invariant `μ` of full support.
   - Co-induced space `X = {f : Γ -> Y : f(γh) = h^(-1)f(γ)}`, `(γ'f)(γ) = f(γ'^(-1)γ)`. A transversal identifies
     `X ≅ Y^(Γ/H)`, a Cantor space.
   - Under `γ`, coordinates are permuted and each is moved by an element of `H`, so `μ^⊗` is invariant; it has
     full support.
   - `Γ ∈ 𝔑`, so `Γ ↷ X` is RF, hence so is `H ↷ X` (restrict the finite actions).
   - `p(f) = f(e)` satisfies `(hf)(e) = f(h^(-1)) = h f(e)`, so it is an `H`-factor map onto the perfect space `Y`.
     RF passes to such factors (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`, item 1).
2. **Finite-index overgroups.** A full-support invariant measure for `Γ` is one for `H`, so `α|_H` is RF, and
   `rf-actions-induce-from-finite-index-subgroups` gives RF of `α`.
