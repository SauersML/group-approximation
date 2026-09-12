---
rg: 2
id: distinct-symbol-patch-linear-reduction-proof
kind: route
title: Break every translate at one coordinate, break the single dangerous translate at a second site, and show all three coordinates cannot be stuck
target: distinct-symbol-patch-ternary-rules-reduce-to-linear-strictness
requires:
  - avoidable-patches-of-affine-rules-inherit-linear-injectivity
artifacts:
  - research/artifacts/distinct-symbol-patch-collision-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Sections 1 and 2 of the artifact.
- **Delta preimage.** `L(d_0) = -epsilon delta_1`, `d = d_0(h^-1 .)`, finite support when `L` is
  bijective. Force `x + d = p` on `hM`.
- **Coordinate `i`.** At sites outside `hM`, keep both configurations off `p_i`. Only `h` and the two
  translates `h m_beta m_i^-1` have their `i`-th site in `hM`. Distinct symbols keep `x + d` off `p` at
  both.
- **Danger at every `i`** forces `d_0 = kappa` on `M` with `kappa S = -epsilon`, and exactly one dangerous
  translate `t = h m_(i+1) m_i^-1` per index after orienting.
- **Second site.** `t` is broken at a free site of position `j` unless `d_0(u_j)` takes one specific value,
  or at a site of `hM` unless one specific relation holds.
- **Linear equation.** `L(d_0)(m_(i+1) m_i^-1) = 0` turns "both `j` fail" into `c_(i+2) = -S`. So all three
  indices stuck would give `S = 0`, a contradiction.
- **Corollary.** Avoidable patches make `L` injective. Theorem 1 makes it non-surjective.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, with no findings.
- **Step 2.** `e` is bijective and `p^-1 e` is a derangement, hence a translation, so `d_0 = kappa`. A transposition inverts the index 3-cycle.
- **Danger translate.** Only `t = h m_(i+1) m_i^-1` is in danger.
- **Stuck sub-cases.** `d_0(u_(i+1)) = kappa`, and `d_0(u_(i+2)) in {kappa, -kappa}`. The value `+kappa` gives `kappa S = 0`, and `-kappa` gives `c_(i+2) = -S`.
- **Re-filling.** Changing `x` at a free `w_j` keeps every other translate broken.
- **Z instance.** Checks.
- **Corollary 3.** The constant-pattern case holds.
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 24.)
