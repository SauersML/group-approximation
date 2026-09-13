---
rg: 2
id: four-strand-burau-faithful-via-parity-correction
kind: route
title: "Burau faithfulness for B_4 from parity-correcting push maps (the Bharathram–Birman–Brendle strategy)"
target: four-strand-burau-representation-is-faithful
requires:
  - brunnian-four-braids-admit-parity-correcting-push
artifacts:
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md
---

This route records the reduction that arXiv:2607.05283v1 (Bharathram, Birman,
Brendle) uses after Proposition 6.4. Each step below was checked in part 1 of
the verification artifact.

**Step 1: no Brunnian kernel element.** Let `Phi != 1` be in `Brun_4` and
suppose `rho_4(Phi) = I`. Take `y`, `Gamma`, `A`, `B` as in
`brunnian-four-braids-admit-parity-correcting-push`.

- Conjugates of kernel elements lie in the kernel, and
  `rho_5(f(Psi)) = rho_4(Psi) (+) 1`. So `f(Phi_1)` acts trivially on
  `H_1(D_5~, p_*~)`.
- Hence the loops bounding regular neighbourhoods of `A` and `B` define the
  same class.
- The Moody polynomial `M(alpha, .)` is determined by that class up to the
  factor `(1 - t)` and a unit `+-t^k`, and `Z[t, t^{-1}]` is a domain. So
  `M(alpha, A) = +-t^k M(alpha, B)`.
- Along an arc, consecutive exponents differ by the signed number of marked
  points of the disk between them (Bigelow 1999, Section 3). If two crossings
  have equal exponents, an even number of odd disks lies between them, and
  parity forces equal signs.
- So neither polynomial has cancellations. The sum of the absolute values of
  its coefficients equals `|A ∩ alpha|`, respectively `|B ∩ alpha|`.
- Multiplying by a unit does not change that sum, so the two counts are
  equal. This contradicts the claim. Hence `ker rho_4 ∩ Brun_4 = 1`.

**Step 2: from Brun_4 to B_4.**

- `ker rho_4` and `Brun_4` are normal in `B_4` and meet trivially, so they
  commute elementwise.
- `Brun_4` is nontrivial, and it is not central, since `Delta^2` is not
  Brunnian.
- The centralizer of a nontrivial noncentral normal subgroup of `B_4` is the
  center `<Delta^2>`. This is Long 1986, Theorem 2.2, as the preprint uses
  it; this lane did not re-read it.
- The reduced Burau image of `Delta^2` is `t^4 I`, so `rho_4` is injective on
  the center.
- Therefore `ker rho_4 = 1`.
