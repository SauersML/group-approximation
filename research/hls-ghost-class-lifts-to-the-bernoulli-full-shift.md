---
rg: 2
id: hls-ghost-class-lifts-to-the-bernoulli-full-shift
kind: claim
title: Some torsion-free host with isometrically embedded expanders carries a full-shift Bernoulli class that vanishes on the tree boundary and has ghost ranks on the marked expanders
distinct_from:
  reduced-group-algebras-contain-no-nonzero-ghosts: that rules out ghost classes inside a reduced group algebra; this asks for a Bernoulli-coefficient class restricting to the HLS ghost, which would refute surjectivity for a wreath product.
  hls-ghost-lift-needs-forest-shift-failure: that is the established reduction of any such class to a forest-shift defect; this is the open existence of one.
refuted_by:
  - hls-ghost-class-never-lifts-to-the-bernoulli-full-shift
---

**REFUTED 2026-09-16 (unreviewed)** by `hls-ghost-class-never-lifts-to-the-bernoulli-full-shift`: over every host
satisfying (M), a full-shift class vanishing on `∂Y` has `r_(x_n)(y) = 0` for all large `n`. The refuted statement
follows.

There are a prime `p` and a torsion-free host `G` satisfying hypotheses (M) and (H-K) of
`hls-ghost-lift-needs-forest-shift-failure`, together with `y ∈ K_0(C_0((Z/p)^G \ {0}) ⋊_r G)` such that:
- `y|_(∂Y) = 0`;
- `r_(x_n)(y) ≠ 0` for infinitely many `n`.

A lift of the HLS class `[p]` along `C_0((Z/p)^G \ {0}) ⋊_r G -> C_0(Ŷ \ {0}) ⋊_r G` is an example.

**What it would give.** Route `bc-bernoulli-defect-via-hls-ghost-lift`: the Bernoulli cylinder comparison is not
surjective, so reduced assembly for `F_p wr_G G` fails to be surjective with trivial coefficients.

## Attempts

- **Reduction (2026-09-13, `hls-ghost-lift-needs-forest-shift-failure`, established).** Under (H-K), any such `y`
  restricts to a forest-shift class outside the cylinder image. Subtracting its cylinder expansion leaves a rank-invisible
  class whose restriction to the tree boundary is nonzero. So the claim needs Baum--Connes surjectivity to fail at the
  forest coefficient (`forest-shift-bernoulli-comparison-is-surjective` false).
- **Gapped lifts.**
  - The natural lift of the HLS operator (induced Laplacian plus identity off the support) loses its gap on long induced
    paths and on partial expanders.
  - Every uniformly gapped local operator over the full shift has local ranks (`bernoulli-pattern-expansions-are-finite`).
  - So a lift, if any, is not the spectral projection of a natural local operator. It has to be built K-theoretically.
- **Traces.** The Haar trace does not see this route, because the forest shift and the marking subshift are Bernoulli
  null sets.
- **Where it stops.**
  - No forest-shift class with nonzero tree-boundary restriction outside the cylinder image is known over any group.
  - If the forest comparison is surjective for a host satisfying (H-K), the claim fails for that host.
- **Refutation (2026-09-16, `hls-ghost-class-never-lifts-to-the-bernoulli-full-shift`).**
  - Restrict to the CND-support shift `T_cnd` instead of the forest shift. Its action is a-T-menable
    (`cnd-support-shift-actions-are-a-t-menable`), so its cylinder comparison is an isomorphism
    (`cnd-support-shift-bc-and-k-amenability`).
  - Large girth puts `∂Y \ {0}` inside `T_cnd`. So (H-K) holds, and reduced assembly at `∂Y` is injective.
  - The key step of the reduction then runs through injective assembly and half-exactness, and ranks at `x_n` vanish
    eventually. Details: `research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Section 6.
