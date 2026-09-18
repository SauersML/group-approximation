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

4. **(bh-free-45, 09-18) For this host, the F_∞ half for all hyperbolic groups reduces to BBMZ
   `quest:F_infty`: F_∞ of the RSG family suffices, and F_∞ of `Γ` is necessary. It is not available from print.**
   - `twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family` (conditional reduction, lane proof):
     - finite-set stabilizers in a full contracting RSG `Γ` are, up to finite index, iterated ascending HNN
       extensions of full RSGs on clopen subsets;
     - so F_∞ for that family makes `SV_Γ` of type F_∞ (Belk–Zaremsky Theorem 4);
     - conversely `SV_Γ` of type F_∞ forces `Γ` of type F_∞.
   - A yes to `quest:F_infty` would therefore settle this node for every hyperbolic group, Kazhdan ones
     included.
   - Checked and not sufficient:
     - BBMZ Theorem 3.1 (`thrm:fin_pres`) gives only finite presentability;
     - the Skipper–Zaremsky question (`contracting-rover-nekrashevych-groups-are-f-infinity`) is itself
       OPEN, and it is the Röver–Nekrashevych special case of `quest:F_infty`.

5. **(bh-free-44, 09-18) Braid groups and bordered mapping class groups: the quasi-isometric half holds.**
   - `braid-groups-quasi-isometrically-embed-in-fp-simple-groups` (ESTABLISHED, lane proof):
     - every `B_n` quasi-isometrically embeds in the finitely presented simple group `SV_Γ`,
       `Γ = Aut_V(V*F_{2n})`;
     - so does every `Mod(S_g^b)` with `b >= 1`, in the corresponding host.
   - Route: cap every hole or boundary circle with a handle, landing in `Map(S_{m,1})`. That group is a
     Lipschitz retract of `Out(F_{2m})` by Hamenstädt–Hensel, `once-punctured-mcg-is-lipschitz-retract-of-out-free`.
     Then lift along the remaining boundary to `Aut(F_{2m})`, and use item 2.
   - Warning, `loop-braid-groups-are-distorted-in-aut-free-groups`: the symmetric-automorphism route
     distorts loop braid groups, by the Handel–Mosher coindex ≥ 2 theorem. So for braid groups the choice of
     embedding into `Aut(F_m)` matters.
   - Still open from Zaremsky's list:
     - the F_∞ half for every class;
     - quasi-isometric embeddings for mapping class groups of punctured surfaces without boundary;
     - closed surfaces, `Out(F_n)` and CAT(0) groups, where even the plain embedding is open.

6. **(bh-free-44, 09-18) More mapping class groups, through a closure theorem.**
   - `undistorted-type-a-class-closure-and-qi-boone-higman` (ESTABLISHED, lane proof): groups undistorted in a
     type (A) actor form a class closed under products and finite extensions, and each of them quasi-isometrically
     embeds in a finitely presented simple group.
   - Consequences for Zaremsky's list:
     - `Mod(S_{0,m})` for every `m`, since its pure subgroup is a direct factor of `PB_{m−1}`;
     - the closed genus-two `Mod(S_2)`, by Birman–Hilden and residual finiteness;
     - dihedral Artin groups;
     - all finite products of these with hyperbolic groups and braid groups.
   - Still open: the QI refinement for `Mod(S_{g,p})` with `g >= 1`, `p >= 1` and no boundary (genus `g = 1`
     with `p = 1` is hyperbolic, so it is covered); `g >= 3` closed; the F_∞ half.
