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
