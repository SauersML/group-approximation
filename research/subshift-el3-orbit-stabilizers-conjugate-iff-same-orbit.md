---
rg: 2
id: subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit
kind: claim
title: The maximal subgroups H_x of EL_3(LC(X,F_2)⋊Z) given by orbit-module stabilizers are conjugate iff x and y lie in one T-orbit
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed)** via `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit-proof`.

Let `X` be an infinite minimal subshift, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`. For `x ∈ X` let `V_x` be the orbit module and `H_x = Stab_G(δ_0 e_1 ∈ V_x^3)`, a maximal subgroup by `subshift-el3-has-continuum-many-maximal-subgroup-classes`.

For `x, y ∈ X` the following are equivalent:
- `H_x` and `H_y` are conjugate;
- the 2-transitive `G`-sets `V_x^3 ∖ {0}` and `V_y^3 ∖ {0}` are isomorphic;
- `V_x ≅ V_y` as `R`-modules;
- `x` and `y` lie in one `T`-orbit.

So these conjugacy classes of maximal subgroups are parametrized exactly by the orbit space `X/Z`.

**Review (sk-verify-15, 2026-09-13): PASS.** Additivity via Fix(G_{v,w}) = {v,w,v+w}, diagonality via root-subgroup fixed sets, R-linearity, and the eigencharacter argument (3)⇒(4) re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part3.md` §3.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived: linearity from the fixed sets of pointwise stabilizers (independent-triple transitivity), diagonality from the root-subgroup fixed sets, R-linearity from e_12 equivariance, and the orbit from LC(X)-eigencharacters. See `research/artifacts/sk-verify-16-2026-09-13.md` §6.
