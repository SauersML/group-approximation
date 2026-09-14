---
rg: 2
id: subshift-elementary-group-diagonal-iso-gives-flip-conjugacy
kind: claim
title: The elementary groups of two infinite minimal subshifts over F_2 admit an isomorphism carrying diagonal onto diagonal iff the subshifts are flip conjugate
distinct_from:
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that open claim concerns arbitrary isomorphisms and orbit equivalence; this claim assumes the isomorphism maps GL_3(LC(X,F_2)) onto GL_3(LC(Y,F_2)) and gets flip conjugacy
artifacts:
  - research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md
---

Let `X, Y` be infinite minimal subshifts with shifts `T, S`. Write:
- `R_X = LC(X,F_2) ⋊_T Z` and `G_X = EL_3(R_X)`, the simple Kazhdan LEF group of `simple-kazhdan-lef-group-from-minimal-subshift`;
- `L_X = GL_3(LC(X,F_2)) = LC(X, GL_3(F_2))`, the diagonal locally finite subgroup of `G_X`.

There is a group isomorphism `α: G_X → G_Y` with `α(L_X) = L_Y` if and only if `(X,T)` and `(Y,S)` are flip conjugate,
i.e. `ψT = S^(±1)ψ` for a homeomorphism `ψ: X → Y`.

How the proof goes:
- the maximal normal subgroups of `L_X` recover `X` (`locally-constant-simple-group-normal-subgroups-are-open-sets`);
- the normalizer of `L_X` acts on `X` through a group between `[[T]]'` and `[[T]]`, whose piecewise closure is `[[T]]`
  (`subshift-elementary-group-rigid-supports-are-mutual-centralizers`);
- isomorphic topological full groups give flip conjugacy (`topological-full-groups-determine-flip-conjugacy`).

Scope:
- This is diagonal-preserving rigidity. It does not decide whether an arbitrary isomorphism `G_X ≅ G_Y` forces flip
  conjugacy. That question stays open in `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.
- Any proof there must also show that a ring isomorphism `R_X ≅ R_Y` forces flip conjugacy (artifact §5).

Status: proved in `subshift-el3-diagonal-iso-flip-conjugacy-proof`, unreviewed.
