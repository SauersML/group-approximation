---
rg: 2
id: hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups
kind: claim
title: Every hyperbolic group quasi-isometrically embeds in a finitely presented simple group of type F_infinity
distinct_from:
  boone-higman-conjecture: that asks only for an embedding; this adds the two refinements Zaremsky prints, an undistorted embedding and a host of type F_infinity, for the class where the plain embedding is known.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN.** M. C. B. Zaremsky, *A taste of twisted Brin–Thompson groups*,
arXiv:2201.00711v1 (TeX main.tex l.495–497):

> Do each of the following groups embed (quasi-isometrically?) into a finitely
> presented simple group (even of type F_∞?) Braid groups, mapping class groups,
> Out(F_n), CAT(0) groups, hyperbolic groups.

The plain-embedding parts are BBMZ survey Problem 5.3 items (settled for hyperbolic
groups by BBMZ, arXiv:2309.06224). This node records the refinements for hyperbolic
groups, where they are the sharpest open part:
- **Type F_∞ host.** Equivalent in spirit to BBMZ-hyperbolic Question 1.2 ("Do full,
  contracting RSGs have type F∞?"), since the BBMZ host is built from a full
  contracting RSG.
- **Undistorted embedding.** Whether the BBMZ embedding (or any embedding into a
  finitely presented simple group) can be taken quasi-isometric. Cyclic subgroups of
  V and of VA are undistorted (Burillo–Cleary–Stein–Taback; Burillo–Felipe
  arXiv:2605.09763), which is consistent with a positive answer; distortion of
  hyperbolic subgroups inside RSGs has not been studied on main.

## Attempts

1. **(bh-free-45, 09-18) The undistorted half is settled.** `hyperbolic-groups-undistortedly-embed-in-fp-simple-groups`
   (ESTABLISHED, lane proof) shows the BBMZ embedding `G <= G*Z <= Γ = [[G*Z | ∂_h(G*Z)]] <= SV_Γ` is
   undistorted at each step:
   - `G <= G*Z` by the free-factor retraction;
   - `G*Z <= Γ` because `G*Z` acts locally faithfully on `∂_h(G*Z)`
     (`g-free-z-acts-locally-faithfully-on-horofunction-boundary`) and label length is subadditive on full
     groups (`full-group-label-length-bounds-distortion`);
   - `Γ <= SV_Γ` because the coordinate-permutation label is locally determined.

   So every hyperbolic group quasi-isometrically embeds in a finitely presented simple group. What remains
   open here is only the type F_∞ requirement on the host. For this host it comes down to BBMZ Question `quest:F_infty` (is `Γ`
   of type F_∞?): Belk–Zaremsky, arXiv:2001.04579, Theorem 4 (`thm:FinitenessTheorem`, proved) makes `SV_Γ` of type F_∞ once `Γ` and its
   finite-set stabilizers on `S` are F_∞, and their Theorem 2 (`thm:quasi-retracts`) with Alonso shows `Γ` must be F_∞. (Correction
   09-18: an earlier version of this entry called their F_n criterion a conjecture; only the sharper
   characterization is conjectural.) Any other undistorted host of type F_∞ would also do.

2. **(bh-free-44, 09-18) The other listed classes, through the BFFHZ host.**
   - The Belk–Zaremsky quasi-retraction is now its own node,
     `twisted-brin-thompson-groups-quasi-retract-onto-acting-group`. In any permutational Boone–Higman
     embedding, only the step from the group into the acting group needs work.
   - `aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups` (ESTABLISHED, lane proof):
     `Aut(F_n)` is a retract of the BFFHZ acting group `Aut_V(V*F_n)`; killing the normal closure of `V`
     gives the retraction. So `Aut(F_n)` is undistorted in the finitely presented simple group `SV_Γ`, and
     every finitely generated `H <= Aut(F_n)` is distorted in `SV_Γ` exactly as it is in `Aut(F_n)`.
   - Braid groups and mapping class groups of non-closed surfaces reach Boone–Higman through `Aut(F_m)`
     (BFFHZ Corollary B). For this host, the "(quasi-isometrically?)" question for them is therefore exactly
     undistortion in `Aut(F_m)`, which is not settled on main.
     - For braid groups, undistortion of `B_n` in `Out(F_{n+1})` would suffice. Hamenstädt–Hensel
       (arXiv:1109.2687) prove only a one-puncture case: `Map(S_{g,1})` in `Out(F_{2g})`.
     - For `Out(F_n)`, closed-surface mapping class groups and CAT(0) groups, the plain embedding is itself open.

3. **(bh-free-45, 09-18) Both refinements hold for cubulated hyperbolic groups and compact special CAT(0) groups.**
   `virtually-compact-special-groups-undistorted-in-2v` (ESTABLISHED, lane proof) uses a different host.
   Every virtually compact special group quasi-isometrically embeds in `2V`, which is simple and of type
   F_∞. This includes every hyperbolic group acting properly and cocompactly on a CAT(0) cube complex. The
   key input is `raags-are-undistorted-in-brin-thompson-group-2v`: Salo's conveyor-belt embedding
   `A_Γ -> 2V` is quasi-isometric, with `|g| <= (ω/2)(M(g)+1)`.
   - The same host covers `B_3`, `GL_2(Z) ≅ Out(F_2)` and `SL_2(Z)`, again with an F_∞ host.
   - For hyperbolic groups the node is now open exactly for the non-cubulated ones, for example infinite
     Kazhdan hyperbolic groups. For those, either BBMZ `quest:F_infty` or a new F_∞ host is needed.
