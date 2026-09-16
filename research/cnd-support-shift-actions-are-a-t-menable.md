---
rg: 2
id: cnd-support-shift-actions-are-a-t-menable
kind: claim
title: The shift action on nonzero configurations whose supports carry a conditionally negative definite word metric is a-T-menable
distinct_from:
  expander-tree-boundary-k0-max-reduced-injective: that is K_0 injectivity of max to reduced at the tree boundary of one expander-marking subshift; this is a-T-menability, in the sense of Baum--Guentner--Willett, for every closed invariant set of CND-support configurations over every finitely generated group.
  forest-shift-bernoulli-comparison-is-surjective: that is Baum--Connes surjectivity at the forest shift, whose configurations need not have a CND word metric on their supports; this is a-T-menability of the CND-support shift, which is a different closed invariant set.
  monster-bc-detector-lives-on-a-proper-orbit-ideal: that imports Finn-Sell's a-T-menability of a boundary groupoid over the Stone--Čech corona; this proves a-T-menability of a transformation groupoid of a Bernoulli subshift, with an explicit function.
---

**ESTABLISHED** by `cnd-support-shift-actions-are-a-t-menable-proof`. Full proof:
`research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Section 3.

**Setting.**
- `G` is a finitely generated group with a finite symmetric generating set and left-invariant word metric `d`.
- `Λ` is a finite set containing `0` with `|Λ| >= 2`. `X = Λ^G` carries the left shift, and `X^0 = X \ {0}`.
- A symmetric kernel `k` on a set `P` with `k(p, p) = 0` is **conditionally negative definite (CND)** if
  `Σ_(i,j) t_i t_j k(p_i, p_j) <= 0` for all `p_1, ..., p_n ∈ P` and real `t_i` with `Σ t_i = 0`.
- The **CND-support shift** is

  ```text
  T_cnd = { x ∈ X : d restricted to F is CND for every finite F ⊆ supp x }.
  ```

**Statement.**
1. `T_cnd` is closed, `G`-invariant and hereditary: `x ∈ T_cnd` and `supp x' ⊆ supp x` imply `x' ∈ T_cnd`.
2. Let `Z ⊆ T_cnd \ {0}` be closed in `X^0` and `G`-invariant. Write the action on the right, `x g = g^(-1)·x`. The action
   is a-T-menable in the sense of Baum--Guentner--Willett, Definition 6.1: there is a continuous `h : Z × G -> R` with
   - `h(x, e) = 0`;
   - `h(x, g) = h(xg, g^(-1))`;
   - `Σ_(i,j) t_i t_j h(x g_i, g_i^(-1) g_j) <= 0` whenever `Σ t_i = 0`;
   - for every compact `K ⊆ Z`, `h` restricted to `{(x, g) : x ∈ K, xg ∈ K}` is proper.

   One such function is `h(x, g) = d(g^(-1) a_0(x), a_0(xg))`, where `a_0` is a locally constant choice of a support
   point.

**Model tests.**
- If `d` is CND on all of `G`, then `T_cnd = X`. Examples are `Z^k` with standard generators and free groups with a
  free basis. There the whole Bernoulli action on `X^0` is a-T-menable, consistent with Higson--Kasparov.
- Every configuration with at most one support point lies in `T_cnd`.

**Scope.**
- Only finite generation of `G` is used. The support hypothesis enters only through distances between points of a single
  support.
- An expander marking `x_n = 1_(A_n)` is not in `T_cnd` for large `n`, by the Poincaré inequality (artifact, Section 5).
  So the non-a-T-menable part of a Gromov monster's marking subshift lies outside `T_cnd`.
