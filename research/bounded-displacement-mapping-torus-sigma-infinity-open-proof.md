---
rg: 2
id: bounded-displacement-mapping-torus-sigma-infinity-open-proof
kind: route
title: "Mapping-cone resolution plus a geometric series over the Novikov ring, uniformly in all degrees"
target: bounded-displacement-mapping-torus-sigma-infinity-open
requires: []
artifacts:
  - research/artifacts/zp-sigma-infinity-mapping-torus-displacement-2026-09-16.md
---

Full details are in the artifact, §§0–4. The notation is that of the claim.

**Inputs (standard, same trust surface as
`bnsr-invariants-stabilize-at-cohomological-dimension-proof`).**

- **(I1) Novikov–Sikorav.** For `Γ` of type `F_∞`, `[ξ] ∈ Σ^m(Γ;Z)` iff the
  Novikov homology `Tor_i^{ZΓ}(\widehat{ZΓ}, Z)` vanishes for `i ≤ m`, for one
  fixed choice of completion, towards `+∞` or `−∞` of `ξ`. Sources: Suciu,
  arXiv:2010.07499, abstract; Sikorav; Bieri; Farber–Geoghegan–Schütz.
  The argument below uses both completions, so the sign convention does not
  matter. Artifact §2 checks on `BS(1,2)` that the correct choice is "towards
  `+∞`".
- **(I2) Comparison.** `Σ^∞(Γ) = Σ^2(Γ) ∩ Σ^∞(Γ;Z)`, from
  `Σ^m = Σ^2 ∩ Σ^m(·;Z)` for `m ≥ 2` (Molyneux–Nucinkis–Santos Rego,
  arXiv:2309.12213, eq. (2.1)).
- **(I3) Openness.** `Σ^2(Γ)` is open (Bieri–Neumann–Strebel, Renz; recorded
  in Ershov–Zaremsky arXiv:2505.18826 §2.1).
- **(I4) Kernel criterion.** For `K ◁ Γ` with `[Γ,Γ] ⊆ K` and `Γ` of type
  `F_m`, `K` is of type `F_m` iff every character vanishing on `K` lies in
  `Σ^m(Γ)` (Zaremsky arXiv:1502.02620, Citation 1.2, after
  Bieri–Geoghegan–Kochloukova). So `±[χ] ∈ Σ^∞(G)`.

**Proof.**

1. **Novikov rings.** `Nov_ξ(Γ)` consists of formal sums with finitely many
   terms below each level of `ξ`, with valuation `v_ξ = min ξ(supp)`.
   - `v(λμ) ≥ v(λ) + v(μ)`, and the same holds for matrices.
   - A square matrix `T` with `v(T) > 0` has `I − T` invertible, with inverse
     `Σ_n T^n` converging entrywise.
2. **Resolution.** Let `P_*` be the based resolution carrying a lift `f'` of
   `φ^{-1}`, and put `F_* = ZG ⊗_{ZN} P_*`.
   - `τ(g ⊗ x) = g t ⊗ f'(x)` is well defined, since
     `g n t = g t φ^{-1}(n)`. It is a `ZG`-chain map lifting multiplication by
     `s` on `Z[G/N] ≅ Z[s^{±1}]`.
   - `1 − s` is injective with cokernel `Z`, so `C_* = Cone(1 − τ)` is a free
     `ZG`-resolution of `Z` of finite type.
3. **Uniform valuation.** For `ξ = aχ + ψ` with `ψ ∈ V`:
   - `Nov_ξ(G) ⊗_{ZG} C_*` is the cone of right multiplication by `I − T_i` on
     `Nov_ξ(G)^{r_i}`, where `T_i = (t c^{(i)}_{jk})` and `c^{(i)}` is the
     matrix of `f'_i`.
   - For `g ∈ supp c^{(i)}_{jk}` we have
     `ξ(t g) = a + ψ(g) ≥ a − ‖ψ‖Δ(f')`.
   - So if `a > ‖ψ‖Δ(f')`, then `v_ξ(T_i) > 0` in every degree, `1 − τ` is a
     chain isomorphism over `Nov_ξ(G)`, its cone is contractible, and
     `Tor_*^{ZG}(Nov_ξ(G), Z) = 0`.
   - Symmetrically, a lift `f` of `φ` and the map `g ⊗ x ↦ g t^{-1} ⊗ f(x)`
     give vanishing for `−a > ‖ψ‖Δ(f)`.
4. **Both completions.** Let `U = {[aχ + ψ] : |a| > ‖ψ‖Δ}`, an open double cone
   containing `±[χ]`. For `[ξ] ∈ U` both `ξ` and `−ξ` lie in `U`, so both
   Novikov completions have vanishing homology in all degrees. By (I1),
   `U ⊆ Σ^∞(G;Z)`.
5. **Homotopical invariant.** By (I4) and (I3), some open `W ∋ ±[χ]` lies in
   `Σ^2(G)`. By (I2), `U ∩ W ⊆ Σ^∞(G)`.
6. **Powers.** `H = ⟨N, t^k⟩ = N ⋊_{φ^k} Z` has index `k`, and
   `ξ|_H = (ka)χ_H + ψ`.
   - Choosing right coset representatives `G = ⊔ H g_i`, splitting supports by
     cosets gives `Nov_ξ(G) ≅ Nov_{ξ|_H}(H) ⊗_{ZH} ZG` as right `ZG`-modules.
   - Since `ZG` is `ZH`-free, Shapiro's lemma for Tor gives
     `Tor_*^{ZG}(Nov_ξ(G), Z) ≅ Tor_*^{ZH}(Nov_{ξ|_H}(H), Z)`.
   - Steps 3–5 for `H` with lifts of `φ^{∓k}` give the stated region
     `k|a| > ‖ψ‖Δ`.
7. **Special cases.**
   - For inner `φ^k = c_{n_0}`, the lifts `x ↦ n_0^{±1} x` have displacement
     `|n_0|_V`.
   - For `N` of type F, a finite-length resolution has finitely many degrees,
     so every lift has finite displacement.
   - Replacing `φ` by `c_{n_0}φ` multiplies a lift by `n_0` and changes `Δ` by
     at most `|n_0|_V`. ∎
