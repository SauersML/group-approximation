---
rg: 2
id: star-compression-design-solves-odd-measure-target
kind: route
title: A self-adjoint compression with x* x = eps_- and q_[0] x = x gives c' q_[0] b' = eps_-
target: odd-measure-crossed-product-unit-below-cylinder-idempotent
requires:
  - odd-measure-crossed-product-has-star-compression-design
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/odd-measure-star-compression-designs-2026-09-12.md
---

Lemma 1.1 of the artifact. The involution `[g] -> [g^-1]` on `F_3[H]` fixes `eps_-` and all functions on
`M_-`. Take `b' = x` and `c' = x*`. Since `q_[0] x = x`, `c' q_[0] b' = x* x = eps_-`.

*Verification by `w3-vf-linear` (2026-09-12), Section 19.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: valid, conditional on the open design claim. x* lies in B because eps_- is central and fixed, and q_[0] x = x gives x* q_[0] x = x* x = eps_-. Precision remark on the finite certificate (artifact Section 5): the partition must refine the F^-1-translates of the read clopens, not only the F^-1 F-translates.*
