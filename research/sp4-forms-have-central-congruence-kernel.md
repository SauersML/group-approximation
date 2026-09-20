---
rg: 2
id: sp4-forms-have-central-congruence-kernel
kind: claim
title: Every simply connected number-field form of Sp_4 that has a real place of real rank two, isotropic or anisotropic, has the congruence subgroup property with S the archimedean places
distinct_from:
  sl3z-finite-index-subgroups-are-congruence-subgroups: that is Bass--Milnor--Serre for the split groups SL_n over Q, with trivial kernel; this is centrality of the kernel for every k-form of type C_2 = B_2, anisotropic forms included, where unipotent methods do not apply.
  sp21-lattice-has-congruence-subgroup-property: that asks for CSP for the rank-one group Sp(2,1), where Serre's conjecture predicts failure; this is a higher-rank classical case, and it is settled by citation.
  bms-congruence-kernel-trivial-not-totally-imaginary: that is the Bass--Milnor--Serre elementary-generation result for SL_n over Dedekind rings; this gives only centrality of the kernel, but for all forms of type C_2, via Kneser--Rapinchuk.
---

**ESTABLISHED** (`sp4-forms-have-central-congruence-kernel-citation`), by citation. The scan of the primary
survey was read. Unreviewed.

## Statement

Let `k` be a number field and `H` an absolutely almost simple, simply connected `k`-group of absolute type
`C_2` (equivalently `B_2`; that is, a `k`-form of `Sp_4`). Let `V_inf` be the set of archimedean places of `k`.
Suppose `H(k_v0)` has real rank 2 at some real place `v0`, for example if some factor of `H(k (x) R)` is locally
isomorphic to `Sp_4(R)`.

Then the congruence kernel `C^(V_inf)(H)` is central in the arithmetic completion of `H(k)`. In other words, `H`
has the congruence subgroup property in the sense of Stover, arXiv:2407.07680v2, p. 11: "C(k) is central in
ˆG(k)", taken for `G(O_k)`.

No isotropy over `k` is assumed. `H` may be `k`-anisotropic, as it must be when an arithmetic lattice in
`Sp_4(R)` built from `H` is cocompact.

## Why this matters here

This removes the only hypothesis in part (H3b) of `deligne-homogeneous-bundle-models-die-at-lattice-residual`.
That part, and the caveat on scope attached to it, needed CSP for the `k`-forms of `Sp_4` behind the cocompact
lattices of `Sp_4(R)`. See `deligne-homogeneous-bundle-models-die-over-every-lattice`.

## Attempts

- 2026-09-20 (swarm-0917-w21-w21-deligne-follow).
  - Kneser 1979 and Raghunathan 1984 (Math. Ann. 266) were looked for, but no text was available from Springer
    or EUDML, so neither is imported.
  - Instead, the numdam scan of Rapinchuk's 1992 Astérisque survey was rendered, and its Theorem 1 was read
    from the page image. The PDF text layer turns every `≥` into `>`. The image shows `B_n (n ≥ 2)`,
    `C_n (n ≥ 2)` and `rang_S G ≥ 2`, and the citation route quotes those.
