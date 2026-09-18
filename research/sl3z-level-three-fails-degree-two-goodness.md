---
rg: 2
id: sl3z-level-three-fails-degree-two-goodness
kind: claim
title: Γ(3) ≤ SL_3(Z) fails degree-two goodness, so this torsion-free residually finite linear Kazhdan group has non-residually-finite central Z/n- and Z-extensions
distinct_from:
  sp21-finite-congruence-kernel-forbids-p-goodness: that derives non-goodness of Sp(n,1)-type lattices in a high degree from a finite congruence kernel; this locates the failure for Γ(3) ≤ SL_3(Z) in degree two exactly, from b_2 = 26 against a finite profinite multiplier.
  sl3z-finite-index-z-extension-centres-stay-bounded: that proves bounded centre orders for any central Z-extension with finite abelianization of a finite-index subgroup of SL_3(Z), without deciding whether one exists; this exhibits one, and draws non-residual-finiteness from the bound.
  degree-two-inflation-onto-makes-z-extension-centres-survive: that is a sufficient condition for unbounded centre survival; this shows the condition fails at Γ(3) by direct counting.
  finite-central-extension-rf-iff-virtually-splits: that is the general criterion; this produces explicit persistent classes for one torsion-free Kazhdan lattice.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that is Deligne's non-RF central Z-extension of Sp_2n(Z), which comes from the universal cover of Sp_2n(R); this is a central Z-extension of a finite-index subgroup of SL_3(Z), whose real group has finite fundamental group, coming from b_2 of the lattice itself.
  sl3z-level-three-congruence-subgroup-has-b2-26: that is the Betti computation; this is its profinite consequence.
---

**ESTABLISHED (unreviewed).** Let `Γ = Γ(3) = ker(SL_3(Z) -> SL_3(F_3))`. Put
`C_0 := |Hom(Γ, Q/Z)| · |H^2_cts(Γ^; Q/Z)|`, which is finite.

Derivation: `sl3z-level-three-degree-two-failure-proof`.

1. **Degree-two inflation is not onto.** For every `n >= 2`,
   `|coker(H^2(Γ^; Z/n) -> H^2(Γ; Z/n))| >= n^26 / C_0`.
   - In particular inflation is not surjective once `n^26 > C_0`, for example at every prime
     `p > C_0^(1/26)` with coefficients `F_p`.
   - So `Γ` is not good. The first failing degree is exactly two, since degree-one inflation is
     an isomorphism and degree-two inflation is injective for every group.
2. **Non-RF finite central extensions.** For each such `n` there is a class `α ∈ H^2(Γ; Z/n)` whose
   central extension `1 -> Z/n -> E_α -> Γ -> 1` has these properties.
   - `E_α` is not residually finite, and `α` is persistent in the sense of
     `finite-central-extension-rf-iff-virtually-splits`.
   - `E_α` is finitely presented, has finite abelianization and has property (T).
3. **A non-RF central Z-extension.** There is a central extension `1 -> Z = <z> -> K~ -> Γ -> 1`
   with the following properties.
   - `K~` is torsion-free, finitely presented and Kazhdan, with finite abelianization.
   - `K~` is **not residually finite**. Some power `z^M ≠ 1` lies in every finite-index subgroup
     of `K~`.
   - The class `c` can be any `c ∈ H^2(Γ; Z)` with nonzero image in `H^2(Γ; R) ≅ R^26`.

**Reading.**
- **The profinite completion cannot see `H^2(Γ; R)`.** By the congruence subgroup property,
  `Γ^` is an open subgroup of `Π_ℓ SL_3(Z_ℓ)`, whose degree-two continuous cohomology is finite.
  Γ carries a 26-dimensional real `H^2`, and all of it is invisible to finite quotients.
- **Class-killing calibrator for goodness arguments.** Γ is:
  - torsion-free, residually finite and residually-3;
  - linear over `Z`, of type F (Borel--Serre, recalled) and Kazhdan;
  - satisfies the Strong Atiyah conjecture (`congruence-kazhdan-groups-satisfy-strong-atiyah`).

  So no argument for degree-two goodness can succeed if it uses only these properties, or
  any combination of them. See the Attempts of `every-hyperbolic-group-is-good`.
- **The invariant.** Let `G` be finitely presented with finite abelianization, and let
  `b = b_2(G)`.
  - If degree-two inflation is onto for trivial `Z/n` coefficients, the count in the proof gives
    `|H^2_cts(G^; Q/Z)[n]| >= n^b / |G^ab|` for every `n`.
  - So for a Kazhdan group with `b_2 > 0`, degree-two goodness needs an infinite profinite
    multiplier, one with `n`-torsion of order `>= n^b / |G^ab|` for every `n`.
  - The first test case of that kind in the graph is the hyperbolic Kazhdan group of
    `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`.

**Not claimed.**
- No value of `C_0`.
- Nothing about levels other than 3.
- Whether `SL_3(Z)` itself is good in degree two. There `b_2 = 0`, by
  `sl3z-schur-multiplier-is-klein-four`.
