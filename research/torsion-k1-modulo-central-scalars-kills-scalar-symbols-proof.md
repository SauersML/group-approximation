---
rg: 2
id: torsion-k1-modulo-central-scalars-kills-scalar-symbols-proof
kind: route
title: Pair a central scalar with GL(R) by commutators of lifts, which kills E(R); then divide the scalar and use K_2 of the algebraic closure
target: torsion-k1-modulo-central-scalars-kills-scalar-symbols
requires:
  - algebraic-closure-kills-rational-steinberg-symbols
---

**Inputs.**
- (K) Kervaire: `K_2(R)` is central in `St(R)`. Weibel, *The K-book*, III Theorem 5.2.1; also Milnor, as quoted in
  Dennis–Stein, LNM 342, p. 245.
- (W) Whitehead: `E(R) = [GL(R), GL(R)]`. Also `E_n(R) ⊆ [GL_n(R), GL_n(R)]` for `n >= 3`, via
  `e_ij(r) = [e_ik(r), e_kj(1)]`. Also `diag(g, g^(-1)) ∈ E_(2n)(R)`.
- (C) For commuting units `r, s` of any ring, the Steinberg symbol is `{r,s} = diag(r, r^(-1), 1) ⋆ diag(s, 1, s^(-1))`,
  where `A ⋆ B = [a, b]` for commuting `A, B ∈ E(R)` with lifts `a, b`. This is well defined, skew-symmetric and
  bilinear. Weibel, *The K-book*, III §5, p. 42, Definition 5.10; Example 5.10.1 gives `{r,s} = [h_12(r), h_13(s)]`.
  Pinned at source by gq-referee-b. The pairing `c` below is Weibel's `⋆`. Agreement with the Dennis–Stein form
  `h(uv)h(u)^(-1)h(v)^(-1)` is Milnor §9, and is not pinned.
- (G) Garland and the tame sequence: for a number field `F`, `1 -> K_2(O_F) -> K_2(F) -> ⊔_𝔭 (O_F/𝔭)^x -> 1` is
  exact, and `K_2(O_F)` is finite. Dennis–Stein §15, p. 257, read at the source by this lane.
- (S) Bass–Tate: `K_2` of an algebraically closed field is torsion-free and divisible. Dennis–Stein §11(ii),
  p. 253, as pinned by gq-referee-b in `algebraic-closure-kills-rational-steinberg-symbols-proof`.
- `K_2` commutes with filtered colimits of rings. Textbook.

**Part 1.**
- *The commutator pairing.* For commuting `P, Q ∈ E(R)`, put `c(P, Q) = [P̃, Q̃] ∈ St(R)` for lifts `P̃, Q̃`.
  - It lies in `K_2(R)`, and by (K) it does not depend on the lifts.
  - For `Q, Q'` both commuting with `P`, `[P̃, Q̃Q̃'] = [P̃, Q̃]·Q̃[P̃, Q̃']Q̃^(-1) = c(P,Q) c(P,Q')`, again by (K).
    The same holds in the first variable.
- *The map `Φ_ν`.* For `g ∈ GL_n(R)`, put `A_ν = diag(ν I_n, ν^(-1) I_n, I_n)` and
  `D_g = diag(g, I_n, g^(-1))`. Both lie in `E_(3n)(R)` by (W), and they commute because `ν` is central. Put
  `Φ_ν(g) = c(A_ν, D_g)`.
  - `g ↦ D_g` is multiplicative, so `Φ_ν : GL_n(R) -> K_2(R)` is a homomorphism into an abelian group. It kills
    commutators, hence `E_n(R)` for `n >= 3` (W).
  - Stabilizing `g ↦ diag(g, 1)` changes `A_ν` only on the new coordinates. There it commutes with `D_g` and is
    supported on disjoint indices, so lifts can be chosen in commuting Steinberg generators. So `Φ_ν` is
    compatible with stabilization.
  - Hence `Φ_ν` defines a homomorphism on `GL(R)/E(R) = K_1(R)`.
- *Units.* For `x ∈ R^x`, `Φ_ν(x) = {ν, x}` by (C), which holds in any ring for commuting units.
- *Multiplicativity in `ν`.* `A_(νν') = A_ν A_(ν')`, all commuting with `D_g`. ∎

**Part 2.**
- For a number field `F`, `K_2(F)` is an extension of a torsion group by a finite group (G), so it is torsion.
- `K_2(Q̄) = colim_F K_2(F)` is therefore torsion, and it is torsion-free by (S). So `K_2(Q̄) = 0`.
- For `ν, μ ∈ Q̄^x`, `Φ_ν(ι[μ]) = {ν, μ}` is the image of a symbol of `K_2(Q̄)` under `Q̄ ⊆ R`, so it is `0`. ∎

**Part 3.** Let `y ∈ K_1(R)`, and choose `n >= 1` and `μ ∈ Q̄^x` with `n y = ι[μ]`. Choose `ν ∈ Q̄` with
`ν^n = λ`. By Part 1, `Φ_λ(y) = Φ_ν(y)^n = Φ_ν(n y) = Φ_ν(ι[μ])`, which is `0` by Part 2. ∎
