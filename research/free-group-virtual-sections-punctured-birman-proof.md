---
rg: 2
id: free-group-virtual-sections-punctured-birman-proof
kind: route
title: Restrict the section to the Dehn--Nielsen--Baer image of the pure mapping class group and read the preimage as the based mapping class group
target: free-group-virtual-sections-give-punctured-birman-sections
requires: []
artifacts:
  - research/artifacts/solve-bh-mcg-outfn-2026-09-13.md
---

Let `S = Σ_{g,k}` with `k ≥ 1`, base point `∗ ∈ S`, and `F = π1(S, ∗) ≅ F_n`.

**Standard inputs, not re-read here.**
- **(DNB) Dehn--Nielsen--Baer for punctured surfaces.** Farb--Margalit, *A Primer
  on Mapping Class Groups*, Theorem 8.8 and the discussion after it.
  - The action on `π1` embeds the extended mapping class group `Mod^±(S)` in
    `Out(F)`, onto the classes preserving the set of peripheral conjugacy classes
    up to inversion.
  - The based version embeds `Mod^±(S, ∗)` in `Aut(F)`, onto the preimage of that
    subgroup.
  - Purity and the orientation character are properties of a representing
    homeomorphism. So a based class and its image after forgetting `∗` have the
    same orientation character and the same action on the punctures of `S`.
- **(BES) The Birman exact sequence.** Farb--Margalit Theorem 4.6, restricted to
  pure groups: `1 → π1(S, ∗) → PMod(S, ∗) → PMod(S) → 1`, with the point-pushing
  map. Under (DNB), point-pushing along `γ` is the inner automorphism `c_γ`, up to
  the convention on inverses.

**Argument.**
1. `Γ_0 = Γ ∩ PMod(S)` has finite index in `PMod(S)`, because `Γ` has finite index
   in `Out(F)`.
2. Take `f ∈ Γ_0`. Then `s(f) ∈ Aut(F)` represents the outer class `f`, which lies
   in the (DNB) image of `PMod(S)`. So `s(f)` lies in the preimage of that image,
   which (DNB) identifies with the subgroup of `Mod^±(S, ∗)` lying over `PMod(S)`.
3. A based mapping class lying over a pure orientation-preserving class is pure and
   orientation-preserving as a class of `S` with the extra marked point `∗`:
   forgetting `∗` changes neither the orientation character nor the action on the
   punctures of `S`, and `∗` is fixed by definition. So `s(f) ∈ PMod(S, ∗) =
   PMod(Σ_{g,k+1})`.
4. By step 2 the forgetful map `PMod(S, ∗) → PMod(S)` sends `s(f)` to `f`. It is
   the restriction of `Aut(F) → Out(F)` under (DNB). Its kernel is `Inn(F) ≅ F`,
   the point-pushing subgroup (BES).
5. So `s|_{Γ_0}` is a homomorphism `Γ_0 → PMod(Σ_{g,k+1})` whose composite with
   forgetting `∗` is the inclusion of `Γ_0`: a splitting of (BES) over `Γ_0`.

The consequence in the target is the contrapositive.
