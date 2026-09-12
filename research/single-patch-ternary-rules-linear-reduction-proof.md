---
rg: 2
id: single-patch-ternary-rules-linear-reduction-proof
kind: route
title: Solve L(d) = -epsilon delta_h, then fill the configuration avoiding the repeated symbol so the patch occurs only at h
target: single-patch-ternary-rules-reduce-to-linear-strictness
requires:
  - avoidable-patches-of-affine-rules-inherit-linear-injectivity
artifacts:
  - research/artifacts/single-patch-ternary-rules-linear-reduction-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Section 1 of the artifact.
- **Delta preimage.** Take `d` with `L(d) = -epsilon delta_h`. It has finite support when `L` is
  bijective.
- **Fill `x`.**
  - On `hM`, set `x` so that `x + d` equals the patch `(s_0, s, s)`.
  - In the involution case `(a^-1 b)^2 = 1`, keep both configurations off `s_0` at `h b a^-1`.
  - At every other site, keep both configurations off `s`.
- **Site lemma.** Twelve ordered pairs of special sites are checked. An occurrence other than `x + d`
  at `h` needs `a` and `b` to commute, or is impossible. `x` cannot occur at `h`, because
  `L(d)(h) != 0`.
- **Collision.** The patch indicator rises by `delta_h` exactly where `L(d)` drops by `epsilon`, so
  `x` and `x + d` have the same image.
- **Corollary.**
  - Abelian memory groups are amenable, and Gromov–Weiss applies there.
  - `avoidable-patches-of-affine-rules-inherit-linear-injectivity` makes `L` injective.
  - Theorem 1.1 makes `L` non-surjective.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently: all twelve site pairs, the
occurrence analysis, the collision, and the three cases of the corollary. There is one arithmetic slip in the artifact:
for `(g*, hb)` the condition gives `b = a^2`, not `b = a^3`. Either way `a` and `b` commute
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 19).
