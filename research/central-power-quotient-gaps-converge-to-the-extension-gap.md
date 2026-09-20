---
rg: 2
id: central-power-quotient-gaps-converge-to-the-extension-gap
kind: claim
title: "Rounding a unitary to an m-th root of unity costs L pi/m in relator defect; so the corona gaps of G/<<z^m>> converge to the gap of G, and z lies in Rad_MF(G) iff those gaps do not decay like 1/m"
distinct_from:
  central-eigencorners-die-over-full-radical-quotients: that passes from an exact eigencorner, or a finite central kernel, to fullness of G; this compares G with its quotients G/<<z^m>> quantitatively, with no eigencorner and no perfectness.
  lifted-thompson-t-mf-radical-dichotomy: that compares Rad(T-bar) with Rad(T) and Rad(C_T(r_k)) qualitatively; this is a general gap inequality for any finitely presented group and any element, whose Thompson instance is the route lifted-thompson-t-not-mf-via-uniform-rotation-centralizer-gaps.
  commutant-projection-extraction: that asks for spectral projections of a central unitary in a relative commutant; this never cuts the spectrum and so never needs a projection.
---

**ESTABLISHED** by `central-power-quotient-gaps-converge-to-the-extension-gap-proof`
(written proof, not Lean-verified; numerical sanity check in
`experiments/central-rounding-2026-09-17/`).

**Setting.**
- `G = ⟨S | R⟩` is finitely presented, `S` finite, and `z ∈ S`.
- `L` is the largest number of letters `z^{±1}` in a relator of `R`.
- For `m ≥ 1`, `G_m = ⟨S | R ∪ {z^m}⟩ = G/⟨⟨z^m⟩⟩`. When `z` is central this is
  `G/⟨z^m⟩`.
- For a tuple `U = (U_s)_{s∈S} ∈ U(k)^S` (any `k`), write `r(U)` for the evaluated relator,
  `def_R(U) = max_{r∈R} ||r(U) − 1||` and `def_m(U) = max(def_R(U), ||U_z^m − 1||)`.
- For `0 < c < 2`, set

  ```text
  δ_∞(c) = inf { def_R(U) : k ≥ 1, U ∈ U(k)^S, ||U_z − 1|| ≥ c },
  δ_m(c) = inf { def_m(U) : k ≥ 1, U ∈ U(k)^S, ||U_z − 1|| ≥ c }.
  ```

  Both are nondecreasing in `c`.

**Statement.**
1. **(Compactness.)** `z ∈ Rad_MF(G)` if and only if `δ_∞(c) > 0` for every `c`. Likewise, the
   image of `z` lies in `Rad_MF(G_m)` if and only if `δ_m(c) > 0` for every `c`.
2. **(Rounding inequality.)** For every `m ≥ 1` and every `c` with `c + π/m < 2`,

   ```text
   δ_∞(c)  ≤  δ_m(c)  ≤  δ_∞(c + π/m) + Lπ/m.
   ```

   Hence `δ_m(c) → δ_∞(c)` as `m → ∞` at every point where `δ_∞` is right-continuous, which
   is all but countably many `c`.
3. **(Criterion.)** Let `M` be any infinite set of positive integers, for example
   `{2^k : k ≥ 0}`. The following are equivalent:
   - (a) `z ∈ Rad_MF(G)`;
   - (b) for every `c`, `inf_{m∈M} δ_m(c) > 0`;
   - (c) for every `c`, `m·δ_m(c) → ∞` as `m → ∞` in `M`;
   - (d) for every `c`, some `m ∈ M` with `m ≥ π/c` has `δ_m(c) > Lπ/m`.
4. **(No intermediate rates.)** Exactly one of the following holds.
   - `δ_m(c) ≥ δ_∞(c) > 0` for all `m` and `c`.
   - There is `c_0 > 0` such that `δ_m(c) ≤ Lπ/m` for every `c ≤ c_0/2` and every
     `m ≥ π/c`.

   So the corona gaps of the quotients `G_m` either stay bounded below uniformly in `m`, or
   collapse at the rounding rate `Lπ/m`. Every rate in between is impossible.

## What this changes

- **A central element of infinite order is never harder than its finite quotients plus one
  rate.** To show `z ∈ Rad(G)` it is enough to show that the finite-order quotients `G_m` have
  gaps beating `Lπ/m` at one `m ≥ π/c` for each `c`. No spectral projection of `ρ(z)`, exact or
  approximate, appears anywhere. So the arc-spectrum failure of the eigencorner method (recorded
  on `lifted-thompson-t-centre-has-commutant-eigencorners`) does not arise.
- **Thompson instance.** For `G = T̄` and `M = {2^k}`, `G_{2^k} ≅ C_T(r_k)` with `z ↦ r_k`
  (`lifted-thompson-t-quotients-are-rotation-centralizers`). So `lifted-thompson-t-is-not-mf` is
  equivalent to uniformity in `k` of the corona gaps of `r_k` in the rotation centralizers. That
  is the hole `rotation-centralizer-rotation-gaps-are-uniform`, used by the route
  `lifted-thompson-t-not-mf-via-uniform-rotation-centralizer-gaps`.
- **The torsion-to-torsion-free passage is not formal, and item 4 says where it lives.** A
  torsion seed family `G_m`, each with full radical, gives nothing for `G` unless its gaps are
  better than `Lπ/m`. Such quantitative gaps must come from the relators of `G` themselves,
  since the relator `z^m` can contribute at most the rounding error.
