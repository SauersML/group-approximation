---
rg: 2
id: lrf-cantor-actions-give-lef-full-and-elementary-groups
kind: claim
title: For minimal topologically free Cantor actions, local residual finiteness equals a combinatorial matricial model of the crossed product, and that one model makes both the topological full group and the elementary groups over F_q LEF
distinct_from:
  residually-finite-actions-give-matricial-crossed-products: that builds an injective matricial model from genuine finite actions; this weakens the hypothesis to partial finite actions, proves the converse through permutation units, and derives LEF of the topological full group from the same model.
  residually-finite-minimal-actions-have-lef-full-groups: that is Ma's Theorem C for full groups alone; this recovers it, under the weaker LRF hypothesis, from the ring model that also makes EL_n LEF.
artifacts:
  - research/artifacts/un-full-groups-bridge-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route: `lrf-cantor-actions-give-lef-full-and-elementary-groups-proof`.

**Setting.**
- `Γ` is countable and acts minimally and topologically freely on a Cantor space `X` by `α`.
- `R = LC(X,k) ⋊ Γ = A_k(X ⋊ Γ)` for a field `k`.
- `[[α]] ⊆ R^×` via the full bisection units `1_B`.

**Definitions** (artifact §1).
- *LRF.* For every finite `F ∋ e` and `ε > 0` there are a finite nonempty `E ⊆ X` and `β : F -> Sym(E)` with:
  - `β(e) = id`;
  - `β(g)β(h) = β(gh)` whenever `g, h, gh ∈ F`;
  - `d(α(g)z, β(g)z) < ε` on `E × F`.

  Kerr–Nowak residual finiteness implies LRF.
- *Combinatorial matricial model.* An injective unital `Ψ : R -> ∏_ω M_(N_n)(k)` sending every compact open bisection
  unit to a class represented by partial permutation matrices.

**Theorem.** (i) `α` is LRF ⟺ (ii) `R` has a combinatorial matricial model over some field ⟺ (ii') over every field.
These imply:
- (a) `[[α]]` embeds in an algebraic ultraproduct of finite symmetric groups, so `[[α]]` is LEF;
- (b) for `k = F_q`, every finitely generated subgroup of every `GL_m(R)` is LEF. If `R` is finitely generated, then
  `EL_n(R)`, `n >= 3`, is a finitely generated LEF Kazhdan group.

**What it unifies.** One finite model gives three results, restricted either to permutation units or to elementary
matrices:
- Grigorchuk–Medynets (`Γ = Z`);
- Ma's Theorem C (RF actions);
- the LEF rings behind the Pestov 9.1 group and `un-measure`'s Theorem A.

No novelty is claimed for the ingredients. The equivalence (i) ⟺ (ii) and the single-model packaging are this lane's.

**Where it stops.** For `Γ = Z^d`, LRF means genuine finite `Z^d`-actions following `α` on balls (artifact Prop 3.1).
So aperiodic `Z^2`-SFTs have only non-combinatorial ("quantum") models, if any, and the bridge is silent there:
`quantum-matricial-models-separate-full-groups-from-elementary`.
