---
rg: 2
id: fpbs-finite-coset-sandwich-cost-commensurator-rank
kind: claim
title: In a free action of a free group, a sandwich over a non-cyclic finitely generated subgroup K is contained in the commensurator orbit relation wherever its classes hold finitely many K-orbits, and there it costs at least rk Comm(K) ≥ 2
distinct_from:
  fpbs-free-group-sandwich-cost-is-two: that is MC for all sandwiches; this proves the bound on the finite-coset part only and reduces MC to the infinite-coset part.
  fpbs-sandwich-cost-fiber-formula: that prices group-generated and virtually group-generated sandwiches on product actions b × F_2/N; this prices every measurable sandwich, twisted or not, on the set where its classes are finite unions of K-orbits, in every free action.
  fpbs-relative-sandwich-cost-bernoulli-lower-bound: that is the open Bernoulli-minimality statement RBL; this is an absolute lower bound on part of every sandwich, valid in every free action.
artifacts:
  - research/artifacts/fpbs-finite-coset-sandwich-cost-commensurator-rank-2026-09-17.md
---

**ESTABLISHED** through `fpbs-finite-coset-sandwich-cost-commensurator-rank-proof`.

**Setting.**
- `F` is a free group, `a` is a free p.m.p. action of `F` on `(X, μ)`, and
  `K ≤ F` is finitely generated and non-cyclic.
- `E` is a Borel relation with `E_{a|K} ⊆ E ⊆ E_a`.
- `d(x)` is the number of `K`-orbits in `[x]_E`.
- `Y_fin = {d < ∞}` and `Y_∞ = {d = ∞}`. Both are `E`-invariant.
- `M = Comm_F(K)`.

**Statement.**
1. `[M:K] ≤ #(K\V(T_K)) < ∞`, where `T_K` is the union of the axes of
   `K` in the Cayley tree.
2. For a.e. `x ∈ Y_fin`, `[x]_E` is a union of at most `[M:K]` `K`-orbits
   lying in `Mx`. So `E|Y_fin ⊆ E_{a|M}`.
3. The unnormalized cost satisfies `C(E|Y_fin) ≥ rk(M) μ(Y_fin) ≥ 2 μ(Y_fin)`.
   This is sharp at `E = E_{a|M}`.
4. More precisely, on `Y_d` (normalized), `C(E|Y_d) ≥ 1 + (rk K − 1)/d`.
5. If `rk K = 2`, then `M = K` and `E = E_{a|K}` on `Y_fin`.

**Consequence for MC.** For `F = F_2`,
`C(E) ≥ 2μ(Y_fin) + C(E|Y_∞)`. So
`fpbs-free-group-sandwich-cost-is-two` reduces to its infinite-coset part
MC_∞: `C(E|Y_∞) ≥ 2μ(Y_∞)`. Any counterexample must have `μ(Y_∞) > 0`.

**Class kill.** Every sandwich that is a finite union of `K`-orbits per
class, on a set of positive measure, is killed there.
- *Invariant.* `Comm_F(K)`.
- *Death step.* A finite `K`-invariant measure on a countable set lives on
  finite orbits. That forces the coset set `S(x)` into `K\Comm(K)`, and the
  covering-relation induction formula then prices it at `rk Comm(K)`.

This is exactly the mechanism of the cheap unconstrained example: cost 3/2
containing `F_2` with index 2. Inside `E_a` it cannot occur below cost 2.
