---
rg: 2
id: fp-simple-groups-have-no-models-through-classical-products
kind: claim
title: A finitely presented infinite simple group has no hyperlinear or sofic model through finite groups whose bounded-depth derived subgroup is theta-gapped, such as unboundedly long products of general linear groups
distinct_from:
  fp-simple-groups-have-no-classical-group-unitary-models: that treats finite groups whose commutator subgroup is a single quasisimple classical group; this treats targets whose L-th derived subgroup lies in the product-and-quotient closed class of constituent-gapped groups, which covers unboundedly many classical factors
  perfect-group-relator-width-over-nilpotent-groups: that bounds relator width over nilpotent groups for weak models with any bi-invariant length; this concerns trace-metric hyperlinear and sofic models, and pushes them into bounded-depth derived subgroups instead of bounding a width
---

**ESTABLISHED (lane sk-trace-template, 2026-09-13, unreviewed).** Proof: `fp-simple-groups-have-no-models-through-classical-products-proof`.

Let `S` be a finitely presented infinite simple group. Fix `θ < 1` and `L ≥ 0`, and let `𝒢_θ` be the class of
`constituent-gapped-finite-groups-closed-under-products`. Then `S` has no finite-group hyperlinear model
(`fp-simple-models-concentrate-on-template-constituents`) in which every target has `Q_k^{(L)} ∈ 𝒢_θ`, where `Q^{(L)}` is the
`L`-th derived subgroup.

**Instances.**
- `L = 0`, `θ = 2^{−1/481}`: `Q_k` any quotient of a finite direct product `∏_{i ≤ m_k} Γ_{k,i} × A_k`, with `Γ_{k,i}`
  quasisimple classical, `A_k` abelian, and `m_k` unbounded.
- `L = 4`: `Q_k = ∏_{i ≤ m_k} GL_{N_i}(q_i)`, in any ranks, over any fields, with any number of factors. The standard facts
  used, recalled rather than re-read (e.g. Taylor, *The Geometry of the Classical Groups*, Ch. 4), are:
  - `[GL_N(q), GL_N(q)] = SL_N(q)` for `(N,q) ≠ (2,2)`;
  - `SL_N(q)` is perfect, hence quasisimple, for `(N,q) ∉ {(2,2),(2,3)}`;
  - `GL_2(2) ≅ S_3` has derived length 2, and `GL_2(3)` has derived length 4.

  So `Q_k^{(4)}` is the product of the quasisimple `SL_{N_i}(q_i)` over the non-exceptional factors.
- *Sofic.* Permutation representations are unitary representations, so the same targets give no sofic model of `S` through
  their actions on finite sets.

**What it removes.**
- It closes the "unbounded direct products of gapped groups" room recorded on
  `fp-simple-groups-have-no-classical-group-unitary-models`, of which it is the product version.
- *Ring route* (`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`): block-diagonal models into products of general linear
  groups give nothing, whatever the number of blocks.

**What it does not remove.** `𝒢_θ` is not closed under subgroups, and models through subgroups such as `A_m ≤ SL_m(F_q)` are not
excluded. This is where permutation models of sofic groups live. The remaining room is organized on
`fp-simple-finite-group-models-reduce-to-alternating-constituents`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part4.md`):** PASS (§3); item (c) and the classical instances are conditional on `lst-quasisimple-classical-character-ratio-bound`.
