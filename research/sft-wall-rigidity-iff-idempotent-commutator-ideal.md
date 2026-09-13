---
rg: 2
id: sft-wall-rigidity-iff-idempotent-commutator-ideal
kind: claim
title: For a Z^2 SFT, wall certificates are exactly the first-order obstruction to quantum rigidity, equivalently the commutator ideal of the local tiling algebra is idempotent
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that equates finite presentation with commutation of all operator families; this isolates the first-order part, showing that two-dimensional and finitely filtered families fail to commute exactly when two tilings have a disconnected difference set.
  positive-entropy-sft-crossed-products-are-not-fp: that manufactures wall certificates from entropy; this proves wall certificates are the only obstruction visible to extensions, so that shifts without walls can fail rigidity only through an idempotent commutator ideal.
artifacts:
  - research/artifacts/quantum-rigidity-walls-and-commutator-ideal-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `Ω ⊆ A^(Z^2)` an SFT with forbidden patterns in `B_r`,
with `D >= r`. Let `C_D` be the universal algebra of `D`-local tiling families. It has generators `P_z^a`,
relations (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`, and commutator ideal `J_D`. So
`C_D / J_D = LC(Ω, k)`, the predecessor's `A_D` is `C_D ⋊ Z^2`, and `Ω` is `D`-quantum rigid iff `J_D = 0`.

Call `Ω` *`D`-wall-rigid* if for all `T_1, T_2 ∈ Ω` the difference set `{z : T_1(z) != T_2(z)}` is
`2D`-connected. That means any two of its points are joined inside it by steps of sup-length `<= 2D`.

**Theorem.** The following are equivalent:
1. `Ω` is `D`-wall-rigid (no wall certificate at scale `D`);
2. every family on `k^2` commutes;
3. `J_D = J_D^2`;
4. every family with a finite invariant filtration whose subquotient families commute is itself commutative.

**Precise form of the two-dimensional case.** The upper-triangular families with diagonal `(T_1, T_2)` are
`E_a(z) = [[s_a, λ(z)(s_a - t_a)], [0, t_a]]`, with `λ` constant on the `2D`-components of the difference
set. They all commute iff the difference set is `2D`-connected.

**Corollaries.**
- **Composition factors.** Over an algebraically closed field, a noncommuting finite-dimensional family
  for a wall-rigid shift has a composition factor of dimension `>= 3`.
- **Reduction.** Quantum rigidity equals wall rigidity plus `J_D = 0`. For wall-rigid shifts the open
  part is whether the idempotent ideal `J_D` vanishes.

Route: `sft-wall-rigidity-iff-idempotent-commutator-ideal-proof`.
