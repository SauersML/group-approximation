---
rg: 2
id: free-group-full-support-invariant-measure-actions-are-rf-proof
kind: route
title: Rational points of the transport cone give integer counts, and freeness lets each generator act by an independent permutation
target: free-group-full-support-invariant-measure-actions-are-rf
requires: []
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

Artifact part 1, §3, Lemma F, with Lemmas 1–2.

1. **Scales.** By Lemma 2 it suffices to be `δ`-close on `a_i^(±1)`, `i <= m`. Choose a clopen partition `𝒬`
   of small mesh and its refinement `𝒫` by all `a_i^(-1)𝒬`.
2. **Transport cone.** `w(P) = μ(P) > 0` and `w_i(P,P') = μ(P ∩ a_i^(-1)P')` satisfy
   `Σ_(P') w_i(P,P') = w(P) = Σ_(P') w_i(P',P)` by invariance. These are rational linear equations. Rational
   points are dense in the rational subspace of solutions supported on `supp w`, so some integer solution
   `n(P) >= 1`, `n_i(P,P') >= 0` has the same support.
3. **Model.** `E = ⊔ E_P`, `|E_P| = n(P)`. `β(a_i)` is any bijection sending `n_i(P,P')` points of `E_P` into
   `E_(P')`; freeness gives a `Γ`-action (other generators act trivially). Put `ζ(E_P) ⊆ P`.
4. **Closeness.** `n_i(P,P') > 0` forces `P' ∩ a_iP ≠ ∅`, and `a_iP` lies in one atom `Q` of `𝒬`, so
   `P' ⊆ Q`. Hence `ζ(β(a_i)z)` and `a_iζ(z)` both lie in `Q`. `ζ(E)` meets every atom, so it is dense.
5. Lemma 1 (perfectness) turns `ζ` into a Kerr–Nowak model.
