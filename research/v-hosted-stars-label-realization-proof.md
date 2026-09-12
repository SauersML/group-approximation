---
rg: 2
id: v-hosted-stars-label-realization-proof
kind: route
title: Each finite subgroup permutes its own piece labels, and the hypothesis makes these actions agree and intersect exactly
target: v-hosted-stars-without-block-symmetries-occur-in-finite-groups
requires:
  - finite-subgroups-of-thompson-v-permute-a-canonical-partition
  - sofic-amalgam-finite-subgroup-idempotent-traces-are-strict
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

Proof: Section 4 of the artifact (Proposition 4.1).

1. **Faithful label actions.** `psi_s(h)` permutes `P_s` and fixes all other labels. An element of
   `Sigma(P_s)` that fixes every piece is the identity.
2. **Agreement.** An intersection element acts the same way on common pieces, and fixes non-common
   pieces by hypothesis.
3. **Exact intersections.** Take `h in H_s` and `h' in H_t` with equal label images. Both are the identity
   off the common pieces, whose union has complement `union(P_s \ P_t) = union(P_t \ P_s)`, and both are
   the same prefix replacements on the common pieces. So `h = h'`.
4. **Realization.** Theorem 2.6 of the `w4-kap-join` artifact, with the finite group `Sym(Y)`, gives
   positivity.
