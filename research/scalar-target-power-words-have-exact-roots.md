---
rg: 2
id: scalar-target-power-words-have-exact-roots
kind: claim
title: Scalar-target power words t^e = lambda 1 have exact roots in every characteristic, with no p-subtlety
artifacts:
  - research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `scalar-target-power-words-proof`; verification requested from
`w4-vf-linear-b`.

**Statement.** For any field `K`, any `e != 0`, and any `lambda in K^x`, the companion matrix `C` of
`x^e - lambda` satisfies `C^e = lambda 1_e` and `det C != 0`. Hence `t = C (x) 1_d in GL_(ed)(K)` solves
`t^e = lambda 1_(ed)` exactly.

**Consequence.** The pure power word (`l = 1`, `c_0 = c_1 = 1` in the cyclic reduction) is solved with no
rank slack and no amplification beyond `e`. The `p`-divisibility Jordan subtlety recorded under
`rank-ultraproduct-unit-groups-solve-nonsingular-equations` Attempts is therefore confined to
**general-matrix** targets `t^e = M`: there a unipotent block of `M` can fail to be a `p`-th power, and
amplification plus the `(1 + N_(ps))^p` similarity is needed. RGR_p produces a scalar target for pure
powers, which this claim settles unconditionally.

## Attempts

- The single-syllable word `c_0 t^e c_1` has target `t^e = lambda c_0^(-1) c_1^(-1)`, a general matrix;
  it is the established power-word case, not this one.
