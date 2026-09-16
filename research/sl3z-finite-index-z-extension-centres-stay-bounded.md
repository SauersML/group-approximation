---
rg: 2
id: sl3z-finite-index-z-extension-centres-stay-bounded
kind: claim
title: Central Z-extensions with finite abelianization of finite-index subgroups of SL_3(Z) have bounded centre orders in finite quotients, and their pulled-back models round
distinct_from:
  ghb7-finite-index-z-extension-center-survives: that is the open premise that the centre survives at unbounded orders for some finite-index subgroup of GHB_2(7); this proves the opposite for every finite-index subgroup of SL_3(Z).
  sl3-polynomial-finite-index-z-extension-center-survives: that is the open unbounded-survival premise for SL_3(F_q[t]); this proves boundedness for SL_3(Z), where the finitely-dimensionally realizable multiplier is finite.
  z-extension-centre-orders-are-restricted-evaluation-indices: that computes the centre orders as evaluation indices for an arbitrary group; this bounds them for finite-index subgroups of SL_3(Z) through finiteness of the realizable multiplier, without computing any evaluation index.
  degree-two-inflation-onto-makes-z-extension-centres-survive: that gives a sufficient condition for survival at every order; this shows that survival is bounded for finite-index subgroups of SL_3(Z), so that condition fails wherever such an extension exists.
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that is the general rounding criterion for models pulled back from a Kazhdan cover; this verifies the fixed-mass condition for every central Z-cover with finite abelianization of a finite-index subgroup of SL_3(Z).
---

**Setting.**
- `K <= SL_3(Z)` has finite index.
- `1 -> Z = <z> -> K~ -> K -> 1` is a central extension with class `c ∈ H^2(K; Z)`.
- `K~` has finite abelianization.
- `R(K)` is the set of finite-dimensionally realizable classes in `H^2(K; T)`. It is a finite
  subgroup by `sl3z-finite-index-fd-projective-multiplier-is-finite`.
- `Λ` is the image of `H^2(K; Z) -> H^2(K; R)`, and `c_R` is the image of `c`.

**Statement.**
1. **The class is archimedean.** `c` has infinite order and `c_R != 0`, so `b_2(K) > 0`.
   - At level one, `H_2(SL_3(Z); Z)` is finite (`sl3z-schur-multiplier-is-klein-four`), so
     `SL_3(Z)` itself has no such extension.
2. **Divisibility.** `{t ∈ R : t c_R ∈ Λ} = (1/m)Z` for a unique integer `m >= 1`. Put
   `C := m·|R(K)|`.
3. **Bounded eigenvalues.** For every finite-dimensional unitary representation `ρ` of `K~`,
   every eigenvalue of `ρ(z)` is a root of unity of order at most `C`.
4. **Bounded centre orders.** For every homomorphism of `K~` onto a finite group, the image of
   `z` has order at most `C`. In the notation of
   `z-extension-centre-orders-are-restricted-evaluation-indices`, `sup_N e(N) <= C`.
5. **Pulled-back models round.** `K~` has property (T).
   - Let `ρ_k : K~ -> U(d_k)` satisfy `||ρ_k(z) - 1||_(2, d_k) -> 0`, and let `E_k` be the
     projection onto `Fix ρ_k(z)`. Then
     `1 - tr_(d_k) E_k <= ||ρ_k(z) - 1||_(2, d_k)^2 / (4 sin^2(π/C))` when `C >= 2`, and
     `E_k = 1` when `C = 1`.
   - Hence, for any section `s : K -> K~`, the asymptotic representations `ρ_k ∘ s` of `K`
     round strictly, by `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`.

Derivation: `sl3z-z-extension-centres-bounded-proof`.

**Reading.**
- **The template has no instance here.** The graph's central-extension route to flexible
  HS-instability needs a Kazhdan central `Z`-cover whose centre survives at unbounded orders in
  finite quotients. The central scalars `e^(2πi/k)`, `k -> ∞`, are then almost trivial in
  normalized Hilbert--Schmidt norm but have no fixed vectors. This is
  `rf-kazhdan-group-not-flexibly-hs-stable`, and the open premises at `GHB_2(7)` and
  `SL_3(F_q[t])`. By items 4 and 5, no finite-index subgroup of `SL_3(Z)` supplies such a cover,
  and every model pulled back through one rounds.
- **Degree-two goodness.** By contraposition of
  `degree-two-inflation-onto-makes-z-extension-centres-survive`, a finite-index `K` that has
  one extension as in the setting fails (G2): some class in some `H^2(K; Z/n)` is not inflated
  from a finite quotient.
- **Where the finiteness comes from.** The bound only uses finiteness of `R(K)`, and the
  argument runs backwards too. For any group, a central `Z`-extension with finite abelianization
  whose centre survives at unbounded orders makes `R` infinite, because the eigenspace classes of
  the proof have unbounded orders.
  - *Model test.* The Heisenberg cover of `Z^(2g) ⋊ Sp_(2g)(Z)` in
    `rf-kazhdan-group-not-flexibly-hs-stable` is such an extension, so that group has infinite
    `R`. There the rotation classes come from `Z^(2g)`, which has no analogue inside a
    finite-index subgroup of `SL_3(Z)`.
  - *Classical phenomenon of the same kind (recalled, not load-bearing).* Deligne's failure of
    residual finiteness for the universal-cover lattice over `Sp_(2n)(Z)`
    (`deligne-universal-cover-lattice-is-non-rf-kazhdan`).

**Not claimed.**
- Nothing about asymptotic representations of `K` that are not pulled back from a central
  `Z`-cover.
- Nothing about non-central kernels.
- Nothing about `SL_3(Z)` beyond its finite-index subgroups; in particular, whether
  `SL_3(Z)` is flexibly HS-stable stays open.
- No explicit value of `C`. Whether any congruence subgroup has `b_2 > 0`, so that the setting
  is non-vacuous, is not decided here.

## Attempts

- 2026-09-16 (swarm-sl3-z-weakly-ucp-stable): derived from
  `sl3z-finite-index-fd-projective-multiplier-is-finite` through an eigenspace argument. It is
  recorded as an obstruction to attacking `sl3-z-weakly-ucp-stable` through visible central
  extensions.
