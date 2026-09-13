---
rg: 2
id: thompson-steinberg-three-generator-presentation-proof
kind: route
title: Rerun the Thompson-Steinberg comparison over the two-generator presentation of V
target: thompson-steinberg-three-generator-presentation
requires: [leavitt-unit-group-steinberg-weyl-presentation, bleak-quick-finite-presentations-of-thompson-v, thompson-v-finitely-presented-infinite-simple]
artifacts:
  - research/artifacts/thompson-steinberg-three-generator-variant-2026-09-12.md
  - research/artifacts/thompson-steinberg-presentation-2026-09-12.md
  - experiments/nonsofic-certificates/presentations/verify_thompson_steinberg_uv.py
  - experiments/nonsofic-certificates/presentations/thompson-steinberg-uv-presentation.json
---

The proof is Steps 0-5 of `research/artifacts/thompson-steinberg-presentation-2026-09-12.md`,
with three substitutions recorded in the variant artifact.
1. Step 0: `<u,v | Theorem 1.3> = V` (`bleak-quick-finite-presentations-of-thompson-v`, item 3).
2. Step 1: `iota_1(u)` and `iota_1(v)` generate the elements supported on the cone `1`, since `u`
   and `v` generate `V`.
3. Step 5: `u^3 = (00 01)` dies modulo the transvection subgroup, by `(u^3x)^3 = u^6 = 1`.

Everything else is unchanged. Well-definedness and transport of leaf transvections; the derived
Steinberg laws from splitting; the homomorphism from the sixty-relator group
`leavitt-unit-group-steinberg-weyl-presentation`, with `t -> u^3`; injectivity through the
exact images; surjectivity through normality and simplicity of `V`
(`thompson-v-finitely-presented-infinite-simple`).

The exact computation (MSI, PASS) certifies what the argument consumes: the sixteen relators
hold in `L^x`; `u^3 = U_(00 01)`; the eleven conjugator predicates; and the images `iota_1(u)`,
`iota_1(v)`.
