---
rg: 2
id: scalar-target-power-words-have-exact-roots
kind: claim
title: Scalar-target power words t^e = lambda 1 have exact roots in every characteristic, with no p-subtlety
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
  - research/artifacts/gk-vf-linear-b-verification-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `scalar-target-power-words-proof`. Verified by `w4-vf-linear-b` (Section 30.2
of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`), which asked for the `e < 0` case to be
stated.

**Statement.** For any field `K`, any `e != 0`, and any `lambda in K^x`, `t^e = lambda 1` has an exact
solution in `GL_(|e|)(K)`, hence in `GL_(|e|d)(K)` after tensoring with `1_d`.
- **`e > 0`.** The companion matrix `C` of `x^e - lambda` satisfies `C^e = lambda 1_e` and `det C != 0`;
  take `t = C`.
- **`e < 0`.** `t^e = lambda 1` iff `(t^(-1))^|e| = lambda 1`, so take `t = C^(-1)` with `C` the companion
  matrix of `x^|e| - lambda`. Alternatively take `t` to be the companion matrix of `x^|e| - lambda^(-1)`.

**Consequence.** The pure power word (`l = 1`, `c_0 = c_1 = 1` in the cyclic reduction) is solved with no
rank slack and no amplification beyond `|e|`. The `p`-divisibility Jordan subtlety recorded under
`rank-ultraproduct-unit-groups-solve-nonsingular-equations` Attempts is therefore confined to
**general-matrix** targets `t^e = M`: there a unipotent block of `M` can fail to be a `p`-th power, and
amplification plus the `(1 + N_(ps))^p` similarity is needed. RGR_p produces a scalar target for pure
powers, which this claim settles unconditionally.

## Attempts

- The single-syllable word `c_0 t^e c_1` has target `t^e = lambda c_0^(-1) c_1^(-1)`, a general matrix;
  it is the established power-word case, not this one.
