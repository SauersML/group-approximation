---
rg: 2
id: biasymptotic-subshift-complement-ideal-is-ultramatricial
kind: claim
title: If every point outside a subsystem Y has both limit sets in Y, the ideal I_Y of LC(X,F_2)⋊Z is a union of finite matrix subrings over F_2
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `biasymptotic-complement-ideal-ultramatricial-proof`.

Setting:
- X ⊆ A^Z is a subshift and Y ⊆ X is closed and invariant.
- Suppose α(x) ∪ ω(x) ⊆ Y for every x ∈ X∖Y.

Conclusion: every finite subset of I_Y = {Σ f_j u^j : supp f_j ∩ Y = ∅} lies in a subring with a unit e_V that is isomorphic to a finite product of matrix rings M_k(F_2). So `ultramatricial-ideals-have-elementary-congruence-kernels` applies to I_Y.

The limit-set hypothesis is what this proof uses. A corner e_V R e_V whose V meets a minimal set outside Y is not locally finite. (Corrected per sk-verify-22 §2, 2026-09-14. The earlier remark said "a recurrent orbit outside Y", which is false for a recurrent non-minimal orbit: in `recurrent-orbit-closure-with-unique-sturmian-minimal-set` the kernel onto the Sturmian subsystem is locally finite. The weaker hypothesis that Y contains every minimal subset of X suffices, by `minimal-set-complement-ideal-is-ultramatricial`.)

**Review (sk-verify-5, 2026-09-13): PASS. Compactness bound on J-chains, transitivity of ~, closure under products, matrix units from distinct class members, and the finite subrings ⊕M_k(F_2)^c ⊆ I_Y were re-derived.** See `research/artifacts/sk-review-5-2026-09-13-part2.md` §1.
