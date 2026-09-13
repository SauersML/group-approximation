---
rg: 2
id: fg-simple-line-groups-have-no-one-sided-supports-proof
kind: route
title: Elements that are trivial near an end form a proper normal subgroup, and end germs of finite-breakpoint maps land in solvable groups
target: fg-simple-line-groups-have-no-one-sided-supports
requires: []
artifacts:
  - research/artifacts/zp-left-orderable-simple-type-f-fences-2026-09-13.md
---

Artifact §2 (Lemma B, Corollary B1, Remark B2) and §3 (Lemma C, Corollary C1).

1. **Restriction.** Each `g ∈ G` fixes the endpoints of `C`, so `g(C) = C`. The kernel of the restriction
   to `C` is normal and is not `G`, because points of `C` are moved. So it is trivial, and `G` acts
   faithfully on `C` without global fixed points.
2. **Item 1.** Let `K_+` be the set of elements that are the identity near the right end of `C`. It is a
   subgroup, and it is normal because conjugation carries a terminal segment to a terminal segment. If
   `K_+ = G`, then each of finitely many generators is the identity beyond some point. Beyond the largest
   such point every element is the identity, which gives a global fixed point in `C`. So `K_+` is a proper
   normal subgroup, and simplicity gives `K_+ = 1`. Likewise at the left end.
3. **Item 2.** An element of `G_I` with `I ⊊ C` fixes a neighbourhood of at least one end of `C`
   pointwise, so it is trivial by item 1.
4. **Item 3.**
   - At `±∞`, a finite-breakpoint PL map, or a finitely-piecewise projective map fixing `∞`, is eventually
     affine.
   - At a finite endpoint `a` fixed by `G`, PL germs are `x ↦ a + λ(x − a)`. Projective germs are
     conjugate to affine germs by `x ↦ 1/(x − a)`.
   - So the germ map at each end of `C` is a homomorphism from `G` to a solvable group. Since `G` is
     nonabelian simple, its kernel is `G`. That contradicts item 1 unless `G = 1`.
