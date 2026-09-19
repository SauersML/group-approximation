---
rg: 2
id: thompson-f-finite-rank-median-actions-fix-a-copy-of-f
kind: claim
title: In every action of Thompson's F on a finite-dimensional CAT(0) cube complex or complete finite rank median space, and in every semi-simple action on a complete CAT(0) space of finite dimension, finitely generated subgroups of F' have finite orbits, so some point stabilizer contains a finite-index subgroup of a copy of F; amenable-stabilizer routes to amenability of F through finite-dimensional nonpositively curved hosts are root-equivalent
distinct_from:
  cubical-hosts-of-thompson-f-never-have-property-a: that treats actions with finite stabilizers (cd F = infinity forces infinite dimension); this treats every action on a finite-dimensional host, whatever the stabilizers, and shows one stabilizer always contains a copy of F up to index 2^dim.
  stein-farley-height-fixes-a-roller-boundary-point: that is about the one infinite-dimensional Farley complex; this is about all finite-dimensional (and finite rank median, and semi-simple finite-dimensional CAT(0)) hosts at once.
  thompson-f-hyperbolic-actions-have-a-finite-boundary-orbit: that is the Gromov-hyperbolic host class; this is the finite-dimensional cubical, median and CAT(0) class, where the conclusion is a point in the space, not at infinity.
  niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes: that is property (T) giving fixed points in all cube complexes; F has no fixed point in general (F surjects onto Z), and here only F' is locally elliptic, only in finite dimension.
  lifted-thompson-t-perfect-centre-cubically-elliptic: that is about a central element of a lift of T; this is about Thompson's F and its commutator subgroup.
  thompson-f-has-no-free-subgroups: that is the Brin-Squier input used here.
---

**ESTABLISHED** (lane proof, not reviewed) by `thompson-f-finite-rank-median-actions-fix-a-copy-of-f-proof`.

**Setting.** `F` acts on `[0,1]` by dyadic PL maps. `F' = [F,F]` is the set of elements that are the
identity near `0` and `1`, and it is simple (Kato, arXiv:1804.10506, Remark 3.1). For a standard dyadic
interval `I ⊂ (0,1)`, `F_I = {g ∈ F : supp g ⊂ I} ≅ F` is finitely generated and lies in `F'`.

**Theorem.**
1. **(Median / cubical hosts.)** Let `F` act by isometries on a complete median space `X` of finite
   rank `r`. For example, `X` is the vertex set, with the path metric, of a CAT(0) cube complex of
   dimension `r` on which `F` acts by cubical automorphisms. Then every finitely generated subgroup of
   `F'` has an orbit in `X` with at most `2^r` points. In particular, for every standard dyadic
   `I ⊂ (0,1)` there is `x ∈ X` such that `Stab_F(x) ∩ F_I` has index at most `2^r` in `F_I ≅ F`.
2. **(Semi-simple CAT(0) hosts.)** Let `F` act by isometries on a complete CAT(0) space `X` of finite
   topological dimension, and assume the action is semi-simple (every element is elliptic or
   hyperbolic). Then every finite subset of `F'` has a common fixed point. In particular each `F_I`,
   `I ⊂ (0,1)` standard dyadic, fixes a point of `X`.
3. **(Sharpness.)** The conclusions do not extend to `F`: `F → Z` acting on the line by translations
   has hyperbolic elements. For all of `F'`, which is not finitely generated, nothing is claimed about a
   global fixed point. Only its finitely generated subgroups are controlled.

**Class killed.** The class is *routes to amenability of `F`, or of a group `G ≥ F`, through an action on
a finite-dimensional nonpositively curved host with controlled stabilizers*. Members include:
- Fioravanti's criterion (arXiv:1708.01215, Theorem A(3)): "If all point stabilisers are amenable, Γ is
  amenable";
- the cubical special case: amenable cube stabilizers in a finite-dimensional CAT(0) cube complex;
- proper actions of `F` on such hosts, together with anything built on them (Tits alternative, finite
  asymptotic dimension, boundary amenability);
- the same questions for exactness or other properties that pass to finite-index overgroups.

- *Invariant:* a point `x` with `Stab_F(x) ⊇ K`, where `K` has index at most `2^r` in a copy `F_I ≅ F`.
  In part 2, `K = F_I`.
- *Dying step:* "verify that point stabilizers are amenable". This forces `K` to be amenable, which is
  equivalent to `F` being amenable. Finite index preserves amenability both ways, and `F_I ≅ F`. So:
  - every such route presupposes the root;
  - no proper action exists;
  - exactness routes through stabilizers presuppose exactness of `F`.

**What survives.** Stabilizer information not already contained in `F` can only come from hosts outside
this class:
- infinite-rank median or cubical hosts, such as Farley's complex;
- non-semi-simple actions on finite-dimensional CAT(0) spaces;
- hosts outside nonpositive curvature altogether.
