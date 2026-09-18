---
rg: 2
id: cantor-central-v-elliptic-witnesses-die
kind: claim
title: "Class-kill for central non-rigidity of C(C,Z) ⋊ V: every cnd function bounded on V is bounded on Z·1_C; every V-invariant positive definite φ on C(C,Z) has φ(k·1_U) ≥ φ(1_U) ≥ 0 for every proper clopen U and every k ∈ Z"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that asks boundedness on Z·1_C for all cnd functions on G; this proves it for the cnd functions bounded on V (affine actions with a V-fixed point), and shows every witness against that claim is unbounded on V
  cantor-integer-maps-central-growth-criterion: that reduces central growth to V-almost-invariant spectral laws tending to δ_0; this kills the exactly V-invariant ones, with no hypothesis on their shape
  cantor-integer-maps-sup-norm-is-cnd-dominated: that asks for one cnd function dominating the sup norm; this shows no V-invariant cnd function can even grow along Z·1_U
  brin-thompson-nv-max-type-size-functions-are-not-cnd: that kills max- or range-type functions of the image set; this kills every V-invariant cnd function on C(C,Z), all of which are functions of the image set
  cantor-central-gaussian-scale-mixture-witnesses-die: that kills Gaussian laws that are only almost invariant; this kills laws of every shape that are exactly invariant
  cantor-central-witnesses-have-long-range-dependence: that kills nearly independent cone phases; exactly invariant laws are exchangeable along disjoint cones, and this kills them through de Finetti's directing measure
  extractable-character-spectra-carry-no-almost-invariant-vectors: that kills laws with an equivariant extraction to Prob(C); Haar-type exactly invariant laws have none, and this kills them through positive definiteness instead
  clopen-extractable-spectra-carry-no-almost-invariant-vectors: that kills laws with an equivariant map to probabilities on clopens; this needs no extraction
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that bounds 1_C for commensurating actions; this bounds it for every affine isometric action with a V-fixed point
---

**Setting.** `C = {0,1}^N`, `A = C(C,Z)`, and `G = A ⋊ V` with `(v·f)(x) = f(v^{-1}x)`. A clopen
`U` is *proper* if `∅ ≠ U ≠ C`. Write `e(x) = e^{2πix}`.

**Theorem.**
1. Let `φ` be a positive definite function on `A` with `φ(0) = 1` and `φ(v·f) = φ(f)` for all `v ∈ V`.
   Then for every proper clopen `U` and every `k ∈ Z`, `φ(k·1_U)` is real and `φ(k·1_U) ≥ φ(1_U) ≥ 0`.
2. Let `ψ` be a cnd function on `A` with `ψ(0) = 0` and `ψ(v·f) = ψ(f)` for all `v ∈ V`. Then
   `ψ(k·1_U) ≤ ψ(1_U)` for every proper `U` and `k ∈ Z`, and `ψ(k·1_C) ≤ 4ψ(1_{[0]})`.
3. Let `ψ` be a cnd function on `G` with `sup_{v ∈ V} ψ(v) < ∞`. Then `sup_k ψ(k·1_C) < ∞`.

**Consequence.** Any witness against `cantor-integer-maps-central-direction-has-relative-t` is a cnd
function unbounded on `V`. Equivalently, it is an affine action with no `V`-fixed point, whose
`A`-spectral laws are never exactly `V`-invariant. In the criterion of
`cantor-integer-maps-central-growth-criterion`, the laws `μ_k` must be V-almost invariant but not
V-invariant, with defects that do not vanish. So the whole *fixed-point* class dies. This includes:
- every `ψ(f) = Φ(Im f)` that is a function of the image set;
- every `E g(X(f))` with `X` a random real homomorphism of `V`-invariant law (such an `X` is `0` a.s.,
  proof step 5);
- every Lévy exponent of a `V`-invariant Lévy measure on `Â`;
- stable (`L^α`) constructions whose `‖F(f)‖^α` depends only on `Im f`;
- the *additive split* `ψ(f, v) = ψ_A(f) + ψ_V(v)`, where `ψ_V` is Farley's proper cnd function on
  `V` pulled back along `G → V`, and `ψ_A` is `V`-invariant. This split is cnd, but it is bounded
  on `Z·1_C`, so it is never proper.

So a Haagerup witness for `G` (Problem B(Z)), and hence for R1 on `2V`, must couple the two factors.
Its cocycle on `A` cannot be made `V`-equivariant.

**Invariant, and where every member dies.** The invariant is the exchangeable sequence of cone
phases `χ(1_{[1^{i-1}0]})`. Its partial sums have one law, because all their supports are proper.
Every member dies at de Finetti's directing measure `ν`. Cesàro averaging gives
`φ(k·1_U) = P(ν̂(k) = 1)`, and `{ν = δ_0} ⊆ {ν̂(k) = 1}`.

**Where the argument stops.** Exchangeability of `n` phases uses `n!` elements of `V`, and the Cesàro
step uses all `m`. The argument therefore gives nothing for laws that are `ε`-invariant under a fixed
finite set. Proof: `cantor-central-v-elliptic-witnesses-die-proof`.
