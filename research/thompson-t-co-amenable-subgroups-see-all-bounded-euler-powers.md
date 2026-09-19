---
rg: 2
id: thompson-t-co-amenable-subgroups-see-all-bounded-euler-powers
kind: claim
title: "Every co-amenable subgroup H of Thompson's T keeps every cup power of the bounded Euler class nonzero; so no subgroup that is boundedly acyclic in some even degree, has a finite orbit, or acts on the circle through a Lie group locally isomorphic to SL_2(R) is co-amenable in T"
distinct_from:
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that asks for a co-amenable H with e_R|_H = 0; this is a necessary condition on every co-amenable H, which in that setting turns e_b|_H into a quasimorphism class with non-nilpotent cup powers
  thompson-t-orbits-carry-no-invariant-means: that shows point stabilizers are not co-amenable, using orbit geometry; this is a bounded-cohomology obstruction that also covers subgroups with no finite orbit, e.g. every subgroup conjugate in Homeo(S^1) into PSL_2(R)
  thompson-f-bounded-cohomology-vanishes-separable-duals: that is Monod's vanishing for F; it is used here as one input among several
---

**ESTABLISHED** (by route `thompson-t-co-amenable-bounded-euler-powers-proof`, using imported
literature theorems).

**Notation.**
- `T` acts on `S^1 = R/Z`. `T̄` is the group of lifts to `R`, and `z(x) = x + 1`.
- `rot : T̄ → R` is the translation number.
- For a group `Γ` acting on an oriented circle, `D̄_Γ(γ, η) = rot(f g) − rot(f) − rot(g)`, where
  `f` and `g` are any lifts of `γ` and `η` to `R`. `rot` is normalized by the deck translation
  of that circle.
- `D̄_Γ` is independent of the choice of lifts and bounded by `1`.
- `e_b := [D̄_T] ∈ H²_b(T; R)` is the real bounded Euler class. Its image under the comparison map
  is the real Euler class `e_R` of `T̄ → T` (step 2 of the route). Restriction gives
  `e_b|_H = [D̄_H]` for the restricted action.

**Statement.**
- **(A) Main theorem.** If `H ≤ T` is co-amenable, then `(e_b|_H)^n ≠ 0` in `H^{2n}_b(H; R)` for
  every `n ≥ 1`.
- **(B) Consequences.** `H ≤ T` is not co-amenable in `T` in each of the following cases.
  - **(B1)** `H^{2n}_b(H; R) = 0` for some `n ≥ 1`. For example:
    - `H` is amenable;
    - `H` is boundedly acyclic, e.g. `H ≅ F` or `F^k` (Monod).
  - **(B2)** Some finite-index subgroup of `H` fixes a point of `S^1`.
    - This is an independent proof of (D1) of `thompson-t-co-amenable-subgroup-kills-real-euler-class`.
  - **(B3)** The action of `H` on `S^1` is conjugate, by a homeomorphism of either orientation,
    to `σ ∘ ψ`, where:
    - `ψ : H → G` is any homomorphism;
    - `G` is a connected Lie group locally isomorphic to `SL_2(R)`;
    - `σ` is any continuous action of `G` on a circle.

    This covers:
    - `PSL_2(Z) ≤ T` with its Minkowski-conjugated projective action;
    - every subgroup of any `Homeo_+(S^1)`-conjugate of a subgroup of `PSL_2(R)`, e.g. Fuchsian and
      Schottky subgroups of `T`;
    - lifts of such actions to finite cyclic covers of the circle, via `PSL_2^{(k)}(R)`.
  - **(B3')** Cited, not reproved: the same holds if "conjugate" is weakened to Ghys
    semi-conjugate, because semi-conjugate actions have equal bounded Euler classes (Ghys 1987).
  - **(B4)** `H` is a nonabelian free group, and `e_b|_H = [δφ]` for a quasimorphism `φ` that is,
    up to bounded functions and homomorphisms, `Δ`-decomposable or Brooks. This uses the vanishing
    theorem of Amontova–Bucher.
- **(C) Forced shape for the open claim.** Suppose `H` witnesses
  `thompson-t-co-amenable-subgroup-kills-real-euler-class`, with `u : H̄ → R` and `u(z) = 1`.
  - `rot − u` descends to a homogeneous quasimorphism `φ` on `H` that is not a homomorphism.
  - `[δφ] = ±e_b|_H`, and `[δφ]^n ≠ 0` in `H^{2n}_b(H; R)` for every `n`.
  - So `H` must avoid (B1) to (B4). This strictly extends (D3) of the wave-10 attempt, which
    excluded only the `T`-conjugates of `PSL_2(Z)`.
  - **Free case.** If `H` is free, then `e_R|_H = 0` holds automatically. The target then asks for
    a class in `H²_b(F_r; R)` whose cup powers are all nonzero. Whether cup products of degree-two
    classes of free groups can be nonzero at all is open (Hofmann 2024: "it is not clear whether
    cup products with arbitrary classes in degree 2 vanish"). So a free witness would settle that
    question and give `H^{2n}_b(F_r; R) ≠ 0` for every `n`.

**Calibration: no blanket refutation.** The pair "`e_R = 0` and every `e_b^n ≠ 0`" is realized by
some circle action: `T̄` acting through `T`.
- The pulled-back extension splits, via the diagonal `T̄ → T̄ ×_T T̄`, so `e_R` pulls back to `0`.
- `p^* : H^*_b(T) → H^*_b(T̄)` is an isomorphism, by Gromov's mapping theorem for the amenable
  kernel `⟨z⟩`, so `p^*(e_b)^n ≠ 0`.

Hence "`e_R|_H = 0` forces `e_b|_H` nilpotent" is false for general groups acting on circles.
Theorem (A) constrains the target claim but cannot refute it without information specific to
subgroups of `T`.

**Not claimed.**
- *Nonsingular `T`-spaces.* For a nonsingular `T`-space `X` whose Koopman representation has almost
  invariant vectors, the same transfer argument gives injectivity of
  `H^*_b(T; R) → H^*_b(T; L^∞(X))`. That is a candidate obstruction for
  `thompson-t-euler-class-splits-over-almost-invariant-space`, but no vanishing theorem for the
  resulting `L^0`-quasi-cocycle class is proved here.
- (B3') and (B4) rest on cited theorems that were recalled (Ghys) or read from a secondary source
  (Amontova–Bucher, via Hofmann), not re-derived.
