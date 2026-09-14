---
rg: 2
id: cyclic-factor-subshift-el-2-is-simple-kazhdan-lef-proof
kind: route
title: Write the subshift as a tower over its induced system, then apply the tower identity and EJZ
target: cyclic-factor-subshift-el-2-is-simple-kazhdan-lef
requires:
  - tower-subshift-elementary-group-is-el-3k-of-base
  - elementary-groups-over-fg-rings-have-property-t
  - steinberg-elementary-groups-are-simple-mod-centre
  - minimal-subshift-algebra-is-simple-lef-ring
---

**1. The induced system and the tower.**
- *Minimal.* Let `∅ ≠ Z_0 ⊆ U` be closed and `T^m`-invariant. Then `Z_0 ∪ T Z_0 ∪ … ∪ T^(m−1) Z_0` is closed and `T`-invariant, so it equals `X` by minimality. Since the sets `T^i U` are disjoint, `Z_0 = U`.
- *Infinite.* `X` is the union of `m` homeomorphic copies of `U`, so `U` is infinite.
- *A subshift.* `T` is expansive, so `T^m` restricted to the clopen set `U` is expansive. An expansive homeomorphism of a zero-dimensional compact metrizable space is conjugate to a subshift over a finite alphabet.
- *The tower.* The map `U × {0,…,m−1} → X`, `(x,i) ↦ T^i x`, is a homeomorphism. It sends `S(x,i) = (x,i+1)` to `T^(i+1)x` for `i < m−1`, and `S(x,m−1) = (T^m x, 0)` to `T^m x`. So `X ≅ Y^(m)`.

**2. Rings and groups.** `tower-subshift-elementary-group-is-el-3k-of-base` gives `R_(Y^(m)) ≅ M_m(R_Y)` (its item 2) and `EL_n(M_m(R)) = EL_(nm)(R)` for every `n ≥ 2` (its item 3). Take `n = 2`.

A direct check: the idempotents `e_(T^i U)` are orthogonal and sum to `1`, and `a_i = u^i e_U`, `b_i = e_U u^(-i)` satisfy `a_i b_i = e_(T^i U)` and `b_i a_i = e_U`. So `R_X ≅ M_m(e_U R_X e_U)`. Moreover `e_U u^j e_U = 0` unless `m | j`, so `e_U R_X e_U ≅ LC(U,F_q) ⋊_(T^m) Z = R_Y`.

**3. Simple and Kazhdan.**
- `R_Y` is finitely generated (a subshift algebra), and `2m ≥ 4`. So `EL_(2m)(R_Y)` has property (T) by `elementary-groups-over-fg-rings-have-property-t`, and it is finitely generated.
- `R_Y` is the Steinberg algebra of the transformation groupoid of an infinite minimal subshift, which is minimal and effective. So `EL_(2m)(R_Y)/Z` is infinite and simple by `steinberg-elementary-groups-are-simple-mod-centre`.

**4. LEF for q = 2.** `R_Y` is a LEF ring by `minimal-subshift-algebra-is-simple-lef-ring`. Entrywise models give LEF models of `GL_(2m)(R_Y) ⊇ EL_(2m)(R_Y)`, exactly as in the note l.146–149. Over `F_2` the centre is trivial: `Z ⊆ F_2^× I = {I}` by the steinberg node.
