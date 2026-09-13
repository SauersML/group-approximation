---
rg: 2
id: sylvester-disjoint-cylinder-defects-strictly-submultiplicative
kind: claim
title: Augmentation quotients of Sylvester rank functions on the binary Leavitt unit group algebra multiply disjoint-cylinder defects strictly below independence
distinct_from:
  leavitt-disjoint-cylinder-defects-strictly-submultiplicative: that is the deficit for fixed-point-free rank-ultraproduct models; this asks it for the augmentation quotient of every Sylvester rank function, which covers those models through their rank functions and needs no regular envelope.
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that is the universal assertion that every rank function kills the defect; this is the local quantitative deficit a proof would target, which with near-minimal multiplicativity and the gap is equivalent to it.
artifacts:
  - research/artifacts/sylvester-exact-globality-and-kernel-compression-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `D_A = iota_A(([x_23(1)] - 1)([x_12(1)] - 1))` in `F_2[R^x]`. There is
`theta < 1` with the following property. For every non-augmentation Sylvester matrix rank function `rho` on
`F_2[R^x]`, and all disjoint proper cylinders `A`, `B` with proper union,
`rho_omega(D_A D_B) <= theta rho_omega(D_A) rho_omega(D_B)`.

**What it gives.** Route `sylvester-rank-triviality-via-strict-defect-submultiplicativity`: every Sylvester rank
function kills `D`. So the augmentation rank is the only one, with no regularity.

**Scope.**
- **Model form.** It implies `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` for tuples with proper
  union, since a fixed-point-free model's rank function is its own augmentation quotient.
- **Equivalence.** Given the gap, it is equivalent to `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`.
  If every rank function kills `D`, no non-augmentation `rho` exists and the statement holds vacuously.
  - Only near-minimizers matter.
  - At an exact minimizer the defects are exactly multiplicative (artifact Corollary 3.5), so the content is "no
    minimizer exists".
- **Firewall.** Every sofic subgroup containing both frames carries a free fixed-point-free model with
  `rk(D_A D_B) = (3/8)^2` (`sofic-subgroups-carry-independent-cylinder-defects`), and halving gives `theta = 1`. So a
  relation-only proof must use a nonsofic subgroup containing both frames; otherwise it needs a global input.

## Attempts

- 2026-09-12 `w7-sylv-global` (artifact Section 4). Opened once both inputs of the Sylvester chain, exact globality
  and near-minimal multiplicativity, were proved in class (A). No deficit found. The minimizer numbers of Corollary 3.5
  (multiplicative defects, equality in the triangular count, unchanged corners) are those of the independent firewall
  profile, so nothing proved here separates a minimizer from that profile.
