---
rg: 2
id: root-preserving-subshift-el3-isos-force-orbit-equivalence
kind: claim
title: An isomorphism between the note's simple Kazhdan groups that carries root subgroups to root subgroups forces the two subshifts to be strongly orbit equivalent
artifacts:
  - research/artifacts/sk-rigidity-f2-2026-09-13.md
distinct_from:
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that is the unconditional question for every q and is open; this is the same conclusion under the extra hypothesis that root subgroups are preserved
  subshift-gl3-iso-gives-matrix-ring-iso-odd-q: that uses Zel'manov for GL_3 with q odd; this needs no 1/2 and applies to EL_3 over F_2
---

Let `X` and `Y` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊_T Z`, and `G_X = EL_3(R_X)` the group of
`simple_kazhdan_sofic_group.tex`. Let `α: G_X → G_Y` be an isomorphism carrying the set of six root subgroups of
`G_X` onto the set of six root subgroups of `G_Y`. Then `R_X ≅ R_Y` as rings, and `(X,T)` and `(Y,S)` are strongly
orbit equivalent.

The conclusion is strong orbit equivalence, not flip conjugacy: the ring isomorphism need not carry `LC(X,F_2)`
onto `LC(Y,F_2)`, which is the Cartan-uniqueness question and also firewall F1 of the intrinsic reconstruction
route.

Root-subgroup preservation is the only remaining hypothesis, so it is now the whole content of
`subshift-el3-isomorphisms-are-standard-over-f2`. By `el3-root-subgroups-are-bicommutant-closed` a natural route to it is to show that every maximal abelian
bicommutant-closed subgroup of `G_X` is conjugate to one of the six row or column subgroups, and then that an
isomorphism matches the intersection pattern `A_ij = Row_i ∩ Col_j`. Neither step is proved.
