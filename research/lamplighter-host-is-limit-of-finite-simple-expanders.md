---
rg: 2
id: lamplighter-host-is-limit-of-finite-simple-expanders
kind: claim
title: The lamplighter host EL_3(LC(2^Δ,F_2)⋊(Z/2≀Δ)) over any f.g. infinite LEF group is a marked limit of finite simple groups SL_N(F_2) forming expanders
distinct_from:
  finite-simple-groups-converge-to-simple-kazhdan-group: that is the subshift group over Z with periodic-word models; this is the lamplighter host over every finitely generated infinite LEF group, with configuration (view) models whose generated algebra is a full matrix algebra.
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that proves the host simple, Kazhdan and LEF through models on 2^(Q_n) x Q_n, whose algebra commutes with translations of the base point; this shows the host is a marked limit of finite simple groups forming expanders.
artifacts:
  - research/artifacts/sk-strong-8-finite-simple-limits-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Route: `lamplighter-host-finite-simple-limit-proof`.

Let `Δ` be a finitely generated infinite LEF group with LEF models `(Q_n, φ_n)`. Put `L = Z/2 ≀ Δ` acting on `2^Δ` (shifts plus the flip at `e`), `R = LC(2^Δ,F_2) ⋊ L` and `H = EL_3(R)`. Mark `H` by the `e_ij` of `u_s^{±1}`, `u_a` and `p = 1_[x(e)=1]`.

Then:
1. The models act on `F_2[F_2^(Q_n)]`, the configurations seen from the base point. They are genuine ring homomorphisms from the free algebra on the letters ONTO `M_(2^|Q_n|)(F_2)`, and partial ring homomorphisms from `R` that are eventually nonzero on each nonzero element.
2. `(SL_(3·2^|Q_n|)(F_2), markings) → (H, marking)` in the space of marked groups.
3. `H` and all approximants are marked quotients of the Kazhdan group `EL_3` over the free algebra, so the approximants' Cayley graphs form an expander family.

With `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`, `H` is infinite, finitely generated, simple and Kazhdan.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS; every step re-derived (see the artifact).

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part1.md`):** GAP G1 + repair; the conclusion stands. Items 1–2 re-derived (§2): the view models onto `M_(2^|Q_n|)(F_2)`, eventual multiplicativity, eventual nonvanishing, and marked convergence, all PASS. Item 3 as written fails: the marking `{e_ij(t)}` generates a proper subgroup of `EL_3(F)`, since the augmentation `F → F_2` kills it but not `e_12(1)`, so it is not a Kazhdan set of `EL_3(F)`. Repair (§1): in `H` and in every approximant, `e_ij(1) = [e_ik(u_s), e_kj(u_s^(-1))]` has length 4 in the marking, so a Kazhdan constant `ε` of `EL_3(F)` for `{e_ij(1), e_ij(t)}` gives `ε/4` for the marking, uniformly in `n`. Alternatively, add `e_ij(1)` to the marking.
