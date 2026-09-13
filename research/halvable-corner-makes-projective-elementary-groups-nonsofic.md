---
rg: 2
id: halvable-corner-makes-projective-elementary-groups-nonsofic
kind: claim
title: A halvable corner makes every quotient of the elementary groups by central scalars nonsofic, including the simple quotient
distinct_from:
  halvable-corner-makes-elementary-groups-nonsofic: that makes EL_(nd)(R) itself nonsofic; this carries nonsoficity to EL_(nd)(R) modulo any group of central scalars, which matters because soficity is not known to lift through finite central extensions.
  purely-infinite-simple-algebras-have-nonsofic-el-groups: that is the purely infinite simple class at the level of EL_n; this is the corner lemma at the level of the projective quotients.
artifacts:
  - research/artifacts/un-stability-nonsofic-2026-09-13-part1.md
---

**ESTABLISHED.** Let `k` be a finite field, `R` a countable unital `k`-algebra, `d >= 1` and
`A = M_d(R)`. Suppose `A` has a nonzero idempotent `e` with `eA ≅ eA ⊕ eA` as right `A`-modules.
Let `n >= 2`, and let `C` be any subgroup of the central scalar matrices `k^x · 1` in
`GL_(nd)(R)`. Then the image of `EL_(nd)(R)` in `GL_(nd)(R)/C` is nonsofic.

In particular, if `Z(EL_(nd)(R)) ⊆ k^x · 1`, the quotient `EL_(nd)(R)/Z(EL_(nd)(R))` is nonsofic.
This holds for Steinberg algebras of minimal effective ample groupoids, by
`steinberg-elementary-groups-are-simple-mod-centre`.

**Why a lemma is needed.** `halvable-corner-makes-elementary-groups-nonsofic` gives a nonsofic
subgroup of `EL_(nd)(R)`. Nonsoficity of `G` does not obviously pass to `G/C` for a finite central
`C`, since soficity is not known to lift through finite central extensions. So the nonsofic subgroup
has to meet the scalars trivially. The corner at `e` may be the whole algebra (for `L_k(1,2)`,
`e = 1`), and then its image contains scalars. The fix is to pass to the proper halvable corner
`e' = s_0 t_0`. Proof: `halvable-corner-projective-elementary-groups-nonsofic-proof`.

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: `e' = s_0t_0` is idempotent (`s_0 e = s_0`), nonzero (`t_0 e' s_0 = e`) and proper (`e' s_1 = 0 ≠ s_1`), with `e'A ≅ eA` halvable. The corner map `κ_n(g) = g + (1−e')1_n` is an injective homomorphism into `EL_n(A) ≤ EL_(nd)(R)`. `κ_n(g) = λ1` gives `(λ−1)(1−e') = 0`, so `λ = 1`, and the copy of the nonsofic `EL_n(e'Ae')` meets every group of central scalars trivially. The requires `d-ary-leavitt-groups-nonsofic-over-finite-fields` and `sofic-passes-to-subgroups` are established. `research/artifacts/un-review3-2026-09-13-part2.md` §4.
