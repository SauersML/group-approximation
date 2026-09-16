---
rg: 2
id: cnd-support-shift-bc-and-k-amenability
kind: claim
title: Over every finitely generated group, reduced and maximal assembly at a closed invariant set of CND-support configurations are isomorphisms, and so is max to reduced on K-theory
distinct_from:
  monster-bc-detector-lives-on-a-proper-orbit-ideal: that locates the known monster failure on a proper orbit ideal and imports a-T-menability of a corona groupoid; this proves Baum--Connes and K-amenability at every CND-support subshift of a Bernoulli shift.
  forest-shift-bernoulli-comparison-is-surjective: that asks Baum--Connes surjectivity at the forest shift, which is not a-T-menable in general; this proves the isomorphism at CND-support shifts, a different family of closed invariant sets.
  bernoulli-bc-splits-into-host-and-cylinder-comparison: that reduces Baum--Connes at the full Bernoulli coefficient to the host and the cylinder comparison; this proves the isomorphism at CND-support subshifts with no hypothesis on the host.
---

**ESTABLISHED** by `cnd-support-shift-bc-and-k-amenability-proof`. Full proof:
`research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Section 4.

**Setting.** `G`, `Λ`, `X = Λ^G`, `X^0` and `T_cnd` are as in `cnd-support-shift-actions-are-a-t-menable`.
`Z ⊆ T_cnd \ {0}` is closed in `X^0` and `G`-invariant.

**Statement.** In both degrees:
1. `mu_r : K^top_*(G; C_0(Z)) -> K_*(C_0(Z) ⋊_r G)` is an isomorphism;
2. `mu_max : K^top_*(G; C_0(Z)) -> K_*(C_0(Z) ⋊_max G)` is an isomorphism;
3. `(λ_Z)_* : K_*(C_0(Z) ⋊_max G) -> K_*(C_0(Z) ⋊_r G)` is an isomorphism.

**Instances.**
- `Z = T_cnd \ {0}` for every finitely generated `G`. For torsion-free `G` this gives Corollary E of the artifact: the
  cylinder classes `[1_(C_s ∩ T_cnd)]` over patterns with CND support, one per orbit, form a `Z`-basis of
  `K_0(C_0(T_cnd \ {0}) ⋊_r G)`, and `K_1 = 0` (artifact, Lemma 6.1 and Corollary 6.2).
- The tree boundary of an expander-marking subshift: see `expander-tree-boundary-k0-max-reduced-injective-proof`.

**Scope.**
- No exactness, a-T-menability or Baum--Connes hypothesis on `G` is used.
- The Dirac--dual-Dirac elements are imported in KK form (`a-t-menable-actions-have-tu-dual-dirac-elements`). That form
  rests on BGW's parenthetical remark that Tu works in equivariant KK-theory.
- Descent functoriality and naturality of assembly for `KK^G`-morphisms are standard context (Kasparov 1988;
  Baum--Connes--Higson 1994), not re-read.
