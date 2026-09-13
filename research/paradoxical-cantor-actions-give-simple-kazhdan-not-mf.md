---
rg: 2
id: paradoxical-cantor-actions-give-simple-kazhdan-not-mf
kind: claim
title: A minimal topologically free paradoxical Cantor action with a finite generating clopen family gives an infinite fg simple Kazhdan group with no nontrivial MF quotient
distinct_from:
  boundary-action-elementary-simple-kazhdan-not-mf: that is the free group on its boundary; this is every minimal topologically free Cantor action of a finitely generated group satisfying (H-gen) and (H-par), over a finite field.
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that gives no MF quotient from rank 2n for every groupoid without invariant measure; this adds finite generation, simplicity modulo centre and property (T) from rank 3, using an explicit full defect from an elementary paradox and no Tarski input.
  paradoxical-steinberg-families-kazhdan-no-mf-quotient: that names two families and does not claim simplicity; this is the general transformation-groupoid theorem with simplicity modulo centre.
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; proof in `paradoxical-cantor-actions-give-simple-kazhdan-not-mf-proof`).**

**Setting.** `q` is a prime power, `N >= 3`, and `Γ` acts by homeomorphisms on a Cantor space `X`. Put
`R = LC(X, F_q) ⋊ Γ` (algebraic crossed product). The action is assumed to be minimal and topologically free, and to
satisfy two conditions:
- **(H-gen)** `Γ` is finitely generated, and some finite family of clopen sets has `Γ`-translates separating the
  points of `X`.
- **(H-par)** There are clopen partitions `X = ⊔_(i<=m) A_i = ⊔_(j<=l) B_j` and elements `g_i, h_j ∈ Γ` such that
  all the sets `g_i A_i` and `h_j B_j` are pairwise disjoint (an elementary paradox, `2[X] <= [X]`).

**Statement.**
1. `S_N = EL_N(R)/Z(EL_N(R))` is an infinite, finitely generated, simple group with property (T), and
   `Z(EL_N(R)) ⊆ F_q^× I_N`.
2. For every `n >= 2`, every homomorphism from `EL_n(R)` to an MF group is trivial. Hence every homomorphism from
   `S_N` to an MF group is trivial, and `S_N` is not MF.

**The explicit defect.** `s = Σ_i u_(g_i) χ_(A_i)` and `t = Σ_i χ_(A_i) u_(g_i)^(-1)` satisfy `ts = 1` and
`1 - st = χ_(X \ ⊔ g_i A_i)`. This idempotent is full, with `Σ_j χ_(B_j) u_(h_j)^(-1) (1 - st) u_(h_j) χ_(B_j) = 1`.

**Instances.**
- `north-south-minimal-cantor-action-is-paradoxical` supplies (H-par) whenever some element has north–south dynamics.
- Families: `free-product-finite-groups-boundary-simple-kazhdan-not-mf` and
  `p-adic-projective-line-elementary-simple-kazhdan-not-mf`. The free group on its boundary is the case of
  `boundary-action-elementary-simple-kazhdan-not-mf` over a finite field.

**Model test.** A minimal `Z`-subshift (the Pestov 9.1 ring) carries an invariant probability measure `μ`, and
(H-par) would force `μ(X) >= 2 μ(X)`. So the theorem says nothing there, consistent with that group being LEF.
