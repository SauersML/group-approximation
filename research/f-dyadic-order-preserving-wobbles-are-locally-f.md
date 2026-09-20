---
rg: 2
id: f-dyadic-order-preserving-wobbles-are-locally-f
kind: claim
title: "The order-preserving wobbling group of F's dyadic orbit lies in the dyadic-affine group with rational breakpoints, which is locally conjugate into F by maps carrying D into D; so its action on D is extensively amenable iff F is amenable, and the order gate of the wobbling calibrator is the hole itself"
distinct_from:
  f-dyadic-orbit-geometry-cannot-force-extensive-amenability: that builds a non-order-preserving wobbling calibrator and records the gate W^+(Γ_D) ≤ PL_+([0,1]), so an order-preserving calibrator would be a nonamenable subgroup of PL_+([0,1]); this sharpens the gate to an equivalence, since an order-preserving calibrator exists iff F is nonamenable.
  integral-piecewise-projective-groups-are-locally-subgroups-of-f: that conjugates the integral piecewise projective group on the line into F through Minkowski's ?; this works directly on the dyadic PL side on [0,1], adds control of the dyadic orbit (θ_M(D) ⊆ D), and transfers extensive amenability rather than only amenability.
  pl-ea-calibrators-are-nonamenable-interval-groups: that says a PL world amenable but not EA on breakpoints exists iff PL_+([0,1]) has a nonamenable subgroup; this says that inside the dyadic-affine rational-breakpoint world such a calibrator on D exists iff F itself is nonamenable.
  thompson-f-amenable-iff-dyadic-action-extensively-amenable: that is the equivalence for F ↷ D; this extends it to every group of dyadic-affine homeomorphisms with rational breakpoints and every invariant subset of D.
  rational-breakpoint-dyadic-pl-groups-satisfy-boone-higman: that embeds rational-breakpoint dyadic PL groups on the circle in finitely presented simple groups; this conjugates their interval versions locally into F.
---

**ESTABLISHED** through `f-dyadic-order-preserving-wobbles-locally-f-proof` (lane proof, not reviewed;
elementary, and parts 2–3 may be folklore).

**Setting.**
- `D = Z[1/2] ∩ (0,1)`. `F` is the group of PL homeomorphisms of `[0,1]` with dyadic breakpoints and
  slopes in `2^Z`. `Γ_D` is the Schreier graph of `F ↷ D` for `S = {x_0^{±1}, x_1^{±1}}`.
- `W^+(Γ_D)` is the group of order-preserving bijections `h` of `D` with `sup_t d_{Γ_D}(t, ht) < ∞`.
- `Q_2` is the group of homeomorphisms of `[0,1]` that are piecewise `x ↦ 2^k x + d`, with `k ∈ Z`,
  `d ∈ Z[1/2]` and finitely many pieces. Its breakpoints are automatically rational: at a break,
  `2^k p + d = 2^{k'} p + d'` with `k ≠ k'` gives `p = (d' − d)/(2^k − 2^{k'})`.
- For odd `M ≥ 1`, `A_M = (1/M) Z[1/2]`, and `Q_2^M` is the set of elements of `Q_2` with all breakpoints in `A_M`.

**Theorem.**
1. **(Order gate.)** `F ≤ W^+(Γ_D) ≤ Q_2`, through the unique extension of `h` to `[0,1]`.
2. **(Filtration.)** Each `Q_2^M` is a subgroup, `Q_2^1 = F`, `Q_2^M ∪ Q_2^{M'} ⊆ Q_2^{lcm(M,M')}`, and
   `Q_2 = ⋃_M Q_2^M`. Every finitely generated subgroup of `Q_2` lies in some `Q_2^M`.
3. **(Local conjugacy with the orbit.)** For each odd `M` there is an increasing PL homeomorphism `θ_M` of
   `[0,1]` with `θ_M Q_2^M θ_M^{-1} ≤ F` and `θ_M(D) ⊆ D`. Explicitly, `θ_M = τ_M ∘ σ_M`, where
   `σ_M(x) = Mx` and `τ_M : [0,M] → [0,1]` maps each `[j, j+1]` affinely onto the `j`-th leaf of a fixed
   binary tree with `M` leaves. `Q_2` has no non-abelian free subgroup (Brin–Squier), and it is amenable iff `F` is.
4. **(Extensive amenability transfers.)** Let `H ≤ Q_2` and let `Y ⊆ D` be `H`-invariant. If `F ↷ D` is
   extensively amenable, then so is `H ↷ Y`. Hence the following are equivalent:
   - `F` is amenable;
   - `F ↷ D` is EA;
   - `W^+(Γ_D) ↷ D` is EA;
   - `Q_2 ↷ D` is EA;
   - `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`.
5. **(The gate is the hole.)** Some `H ≤ W^+(Γ_D)` (or `H ≤ Q_2`) has an amenable, non-EA action on `D`
   iff `F` is nonamenable. For `⇐` take `H = F`.

**Class killed.** The class is order-preserving calibration and order-preserving enlargement on the
dyadic orbit geometry.
- *Calibration.* An object that shares with `F ↷ D` the orbit geometry (bounded displacement in `Γ_D`)
  and order preservation, but has an amenable non-EA action on `D`, exists only if the hole is false.
  More generally this holds for any subgroup of `Q_2` acting on any invariant subset of `D`. So no
  counter-calibration can separate "order + orbit geometry" from the hole.
- *Enlargement.* Suppose a proof first makes an order-preserving host act EA, for example `W^+(Γ_D)`,
  `Q_2`, a subgroup of them, or an invariant subset of `D`, and then restricts to `F`. Such a proof proves
  exactly the hole: it gains nothing, and it cannot fail more easily.
- *Invariant.* Local conjugacy into `F` by maps `θ_M` with `θ_M(D) ⊆ D`.
- *Where every member dies.* At the step that passes from `F` to the order-preserving host (or from the
  host to the calibrator). Part 4 turns that host back into a subgroup of `F` acting on an `F`-sub-orbit
  set.

**Consequence for the hole.** The survivor "order preservation plus orbit geometry", which was named on
`f-dyadic-inverted-orbit-is-subballistic-on-rare-events` by the wobbling calibrator, is not an
independent ingredient. The bi-Lipschitz orbit class together with arbitrary wobbles is killed by the
calibrator. With order preservation added, it is equivalent to the root.
