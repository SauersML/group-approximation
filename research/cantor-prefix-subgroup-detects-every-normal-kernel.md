---
rg: 2
id: cantor-prefix-subgroup-detects-every-normal-kernel
kind: claim
title: Every nontrivial normal subgroup of a faithful Cantor homeomorphism group containing V_m intersects V_m nontrivially
distinct_from:
  abstract-btb-simple-quotient-fp-gate: that concerns an abstract construction with a possibly nonfaithful action; this requires an actual subgroup of Cantor homeomorphisms and rules out kernels invisible to its prefix subgroup.
  relative-automorphism-fp-host-reflects-base-presentation: that detects base relators through canonical translations; this detects normal kernels through displaced clopen sets and uses no presentation hypothesis.
artifacts:
  - research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md
---

Let m>=2, let C_m={1,...,m}^N, and let V_m be its Higman--Thompson
group of finite prefix replacements. Suppose

    V_m <= E <= Homeo(C_m).

Every nontrivial normal subgroup N of E meets V_m nontrivially. More
precisely, N contains a nonidentity commutator of two prefix permutations
supported in one cylinder.

Consequently, every homomorphism from E to any group which is injective
on V_m is injective on E. In particular, no homomorphism from a faithful
Scott--Rover--Nekrashevych group V_m(H) can both preserve its V_m subgroup
faithfully and kill a nonidentity localized coefficient L_v(h).

The assertion does not require simplicity of E, finite generation,
contraction, or a finite presentation. It does require a faithful action
on the Cantor set; an abstract group with a nonfaithful action is outside
its scope.

DERIVATION
[[cantor-prefix-normal-kernel-double-commutator-proof]]
