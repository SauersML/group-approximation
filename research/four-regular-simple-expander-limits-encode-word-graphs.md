---
rg: 2
id: four-regular-simple-expander-limits-encode-word-graphs
kind: claim
title: The limits of one four-regular simple expander family are exactly the groups of infinite subshifts with strongly connected word graphs
root: true
distinct_from:
  finite-simple-groups-converge-to-simple-kazhdan-group: that constructs approximants for minimal parameters; this classifies every limit of the explicit degree-four family and bounds model sizes by word complexity alone.
  binary-subshifts-embed-in-three-marked-kazhdan-groups: that embeds all binary subshifts in a marked group space; this characterizes which parameters occur at unbounded dimensions in the specified finite simple family.
artifacts:
  - research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md
---

For the finite marked family from primitive binary words `z` and groups
`Q_z=SL_(3|z|)(F_2)`, the marked limit points as `|z| -> infinity` are
exactly `G_X=EL_3(LC(X,F_2) semidirect Z)` for infinite binary subshifts
whose prefix-suffix word graphs are strongly connected at every level.
The parameter `X` is unique. All these limits are Kazhdan and LEF, and
they are simple exactly when `X` is minimal.

For such an `X`, every relation radius `l>=1` is modeled exactly by one
member with `3N` matrix dimension and
`2l+2<=N<=b_X(2l)`, where
`b_X(r)=p_X(r+1)+(p_X(r+1)-p_X(r))(p_X(r)-1)`.
In the three-generator word metric, `LEF_(G_X)(R)<=2^(9b_X(6R)^2)`
for `R>=1`. For Sturmian `X`, the matrix dimension is at most `12l+6`
and LEF growth is at most `2^(9(12R+2)^2)=exp(O(R^2))`. Choosing models uses the
finite language data; the size bound does not assert a computable choice
for noncomputable subshifts.
