---
rg: 2
id: bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one
kind: claim
title: Barlak–Enders–Matui–Szabó–Winter - every outer Z_2-action on a unital Kirchberg algebra has Rokhlin dimension at most 1, with towers not required to commute
distinct_from:
  outer-actions-on-o2-kk-g-contractible-iff-rokhlin: that proves finite Rokhlin dimension with commuting towers forces KK^G-contractibility on O_2-absorbing algebras; this imports that without commuting towers every outer Z_2-action on a unital Kirchberg algebra already has dimension at most 1.
---

**ESTABLISHED (literature).**  S. Barlak, D. Enders, H. Matui, G. Szabó and
W. Winter, *The Rokhlin property vs. Rokhlin dimension 1 on unital Kirchberg
algebras*, arXiv:1312.6289, read from the PDF text on 2026-09-13.

1. **Definition 1.2** (after Hirshberg–Winter–Zacharias).  For a finite group
   `G` and a unital `A`, `dim_Rok(α) ≤ d` if for all `ε > 0` and finite
   `F ⊂ A` there are positive contractions `f_g^(l)`, `l = 0, …, d`, `g ∈ G`,
   with:
   - `1 =_ε Σ_l Σ_g f_g^(l)`;
   - `α_g(f_h^(l)) =_ε f_(gh)^(l)`;
   - `‖f_g^(l) f_h^(l)‖ ≤ ε` for `g ≠ h`;
   - `‖[f_g^(l), a]‖ ≤ ε` for `a ∈ F`.

   There is no condition relating towers with different `l`.
2. **Theorem 2.3.**  "Let A be a unital Kirchberg algebra and α : Z2 ↷ A an
   action. If α is outer, then α has Rokhlin dimension at most 1."
3. **Mechanism** (proofs of Lemma 2.1, Corollary 2.2 and Theorem 2.3).
   - By Goldstein–Izumi [4, 5.1], `α` is conjugate to `α ⊗ γ`, with `γ` a
     faithful quasi-free `Z_2`-action on `O_∞`.
   - `γ` is conjugate to `⊗_N Ad(u)` on `⊗_N O_∞`, where `u = 1 − 2p` and `p` is
     a non-trivial projection with `[p]_0 = 0` ([4, 6.2]).
   - Lemma 2.1 builds the two towers from projections inside one tensor factor,
     using `[p]_0 = 0`.
   - Corollary 2.2: `γ` has Rokhlin dimension exactly `1`, because no finite
     group action on `O_∞` has the Rokhlin property.
4. **Remark 2.5.**  The action `β : Z_2 ↷ O_2` with
   `O_2 ⋊_β Z_2 ≅ O_∞^st ⊗ M_(2^∞)` from [6, 4.7] has Rokhlin dimension `1`.

**Reading for detection at `p = 2`.**  Combined with item 5 of
`outer-actions-on-o2-kk-g-contractible-iff-rokhlin`:
- every outer `Z/2`-action on `O_2` has Rokhlin dimension at most `1`;
- on `O_2`, finite Rokhlin dimension with commuting towers forces the Rokhlin
  property.

So a counterexample to detection at `2` has Rokhlin dimension exactly `1` (it
is not Rokhlin) and infinite commuting-tower Rokhlin dimension.  The towers of
Theorem 2.3 come from one central copy of `O_∞` on which the action is inner by
a symmetry `1 − 2p` with `[p]_0 = 0`.  At `p = 2` the open problem is whether two
towers can be made to commute, not whether towers exist.

Citation: `bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one-citation`.
