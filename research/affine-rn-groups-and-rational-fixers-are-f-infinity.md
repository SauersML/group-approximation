---
rg: 2
id: affine-rn-groups-and-rational-fixers-are-f-infinity
kind: claim
title: Affine unitriangular Rover–Nekrashevych groups and all finite rational marked stabilizers have type F_infinity
distinct_from:
  aperiodic-point-stabilizers-in-germ-extensions-of-v-are-not-fg: that assumes locally prefix-replacement germs at an aperiodic fixed point; this concerns rational marked points with affine p-scale and q-scale germs.
  zoom-tower-germ-groups-give-f-infinity-germ-extensions: that uses locally realized towers over the cyclic V germ; this needs an actual iterated ascending HNN presentation of affine RN marked fixers.
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

**OPEN — submitted proof pending independent review; not Lean certified; no priority claim.**

For `m≥2,q≥2`, a prime `p∤q`, and every finite number `r≥1` of roots,
let `A=UT_m(Z[1/q])⋊<δ_q>` act on the left-coset tree of
`δ_p^j UT_m(Z_p)`. Its RN group `B_{0,r}` and the pointwise and setwise
stabilizers of every finite subset of `R_r=⊔_r UT_m(Z[1/q])` have type
`F_∞`. The base action on `R_r` is highly transitive, and its isotropy
germs at marked points are `Z²`, with p-scale and q-scale coordinates.

## Attempts

The submitted argument is expanded in artifact §§3–5. The affine action
is proposed to be self-similar by the explicit section formula and
`N_q∩δ_p^j(N)=δ_p^j(N_q)`. The ascending HNN description of `A` supplies
`F_∞`. Skipper–Zaremsky 1709.06524v2 Corollary 4.28 supplies the
single-root finiteness mechanism; the manuscript adapts the split poset
and its descending-link estimates to finitely many roots.

The unresolved main lemma identifies each marked fixer with commuting
ascending HNN extensions of `B_{0,u}×Z^F`. The stable letters contract
disjoint marked balls. One must verify actual conjugation into the base,
normal forms, injectivity when adjoining successive letters, and the
surjectivity argument by removing germs and shrinking neighborhoods.
The detailed proposed proof has not been independently certified. Neither
the ambient group's finiteness nor finite arithmetic script checks prove
this stabilizer statement.
