---
rg: 2
id: heisenberg-group-lies-in-no-z-subshift-elementary-group
kind: claim
title: The integer Heisenberg group, SL_n(Z) for n ≥ 3, and BS(1,2) lie in no GL_m(LC(X,F_q)⋊Z), hence in no G_X
distinct_from:
  every-lef-group-embeds-in-a-z-subshift-elementary-group: that asks whether the Z-family G_X is universal for LEF groups; this gives the counterexample.
  subshift-crossed-product-gl-has-no-distorted-elements: that is the general obstruction; this is its application to explicit groups.
---

**ESTABLISHED (unreviewed).** Let X be any subshift and F_q any finite field.
- The Heisenberg group H = ⟨a,b | [a,c],[b,c]⟩, c = [a,b], is a subgroup of no GL_m(LC(X,F_q)⋊Z). In particular it is a subgroup of no G_X = EL_3(LC(X,F_2)⋊Z).
- The same holds for SL_n(Z) with n ≥ 3, which contains H as its upper unitriangular matrices, and for BS(1,2).

H is finitely generated and residually finite, hence LEF. So the note's Z-family is not universal for LEF groups: Corollary `cor:lef` of the note needs other hosts, the lamplighter crossed products.

**Proof idea.** c has infinite order and c^{n²} = [a^n,b^n], so |c^N| ≤ 12√N. Every infinite-order element of a finitely generated subgroup of GL_m(LC(X,F_q)⋊Z) has positive stable length. In BS(1,2), a^{2^k} = t^k a t^{-k}.

Route: `heisenberg-group-lies-in-no-z-subshift-elementary-group-proof`. Artifact: `research/artifacts/sk-sl3z-bandwidth-distortion-obstruction-2026-09-13.md`.
