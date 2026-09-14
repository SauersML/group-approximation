---
rg: 2
id: elementary-root-subgroups-over-crossed-products-are-not-confined
kind: claim
title: Root subgroups e_ij(R) of EL_n over a crossed product LC(X,k)⋊Z, and all their subgroups, are not confined
---

**ESTABLISHED (unreviewed).**

Let `X` be a compact zero-dimensional space with a homeomorphism `T`, let `k` be a field, `R = LC(X,k) ⋊_T Z`, `n ≥ 3`
and `G = EL_n(R)`. Then for all `i ≠ j`, every subgroup `H ≤ e_ij(R) = {I + rE_ij : r ∈ R}` is not confined in `G`.

**Consequence.** The abelian root subgroups are not obstructions to C*-simplicity of `G_X`
(`cstar-simple-iff-amenable-subgroups-not-confined`, `subshift-elementary-groups-are-cstar-simple`).

**Proof:** `root-subgroups-over-crossed-products-not-confined-proof`.

**Review (sk-verify-13, 2026-09-13, `research/artifacts/sk-verify-13-2026-09-13-part1.md` §1):** PASS. Re-derived Lemma B (top and bottom exponents), the Steinberg commutator `[e_31(u^N), e_12(r)] = e_32(u^N r)`, the conjugate `I + u^N r E_32 + r E_12` (as `E_32E_12 = 0`), the entry comparison, the Weyl-element reduction to `e_12(R)`, and heredity to subgroups. No infiniteness or minimality of `X` is used.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part6.md`):** PASS (§1). Re-derived Lemma A, Lemma B (top and bottom exponents), the Steinberg commutator `[e_31(u^N), e_12(r)] = e_32(u^N r)` by multiplying out, the conjugate `I + u^N r E_32 + r E_12`, the entry comparison, and the Weyl-element reduction. It holds for every compact zero-dimensional `X` and every field `k`. Concurs with sk-verify-13.
