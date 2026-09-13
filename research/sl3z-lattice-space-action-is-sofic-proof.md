---
rg: 2
id: sl3z-lattice-space-action-is-sofic-proof
kind: route
title: Mixing of SL_n(Q_p) on the one-prime S-arithmetic cover, thickened in the real factor, equidistributes the Hecke orbits
target: sl3z-lattice-space-action-is-sofic
requires:
  - finite-equidistributed-orbits-give-sofic-action
  - howe-moore-property-for-simple-lie-and-p-adic-groups
artifacts:
  - research/artifacts/sl3z-lattice-space-hecke-sofic-2026-09-12.md
  - research/artifacts/sl3z-lattice-space-hecke-sofic-part2-2026-09-12.md
---

Full proof: artifact Section 3, then part 2, Sections 4-5. Notation: `G = SL_n(R)`, `Γ = SL_n(Z)`,
`H = SL_n(Q_p)`, `K = SL_n(Z_p)`, `Δ = SL_n(Z[1/p])` diagonal in `G × H`, and `Y = (G × H)/Δ`.

1. **Lemma S1.** `Δ ∩ (G × K) = Γ`. `Δ` is discrete, and dense in each factor, because elementary
   matrices generate and `Z[1/p]` is dense in `R` and in `Q_p`. `Γ` is dense in `K`, and `H = KΔ`.
2. **Lemma S2.** If `D` is a fundamental domain for `Γ` in `G`, then `D × K` is one for `Δ`. So `Y` has
   finite volume.
3. **Lemma S3.** Putting `π((g,h)Δ) = gγ^(−1)Γ` for `γ ∈ Δ ∩ Kh` defines a `G`-equivariant,
   `K`-invariant map `Y → X_n` with `π_* m_Y = μ`. For `a ∈ Δ`, the map `k ↦ π((1,ak)Δ)` pushes Haar
   measure on `K` to the uniform measure on `V(a) = Γ·a^(−1)Γ`. Two facts give this: `Δ ∩ KaK = ΓaΓ`,
   and, by density, the indices `[Γ : Γ ∩ a^(−1)Γa]` and `[K : K ∩ a^(−1)Ka]` are equal.
4. **Lemma S4.** An `H`-invariant vector of `L²(Y)` is a function on `G` invariant under the dense `Δ`,
   hence constant. By Howe--Moore for `SL_n(Q_p)` (Ciobotaru Theorem 1.1, verbatim in the artifact),
   the coefficients on `L²_0(Y)` are `C_0`.
5. **Lemma E.** For `f ∈ C_c(X_n)` and `F = f∘π`, the average of `f` over `V(a)` is
   `∫_K F((1,ak)Δ) dk`. Thickening by a bump `ψ` on a small `U ⊆ G` changes this by at most
   `sup_(u ∈ U, x) |f(ux) − f(x)|`, since `G` commutes with `H` and `π` is `G`-equivariant. The thickened
   quantity is the matrix coefficient `⟨λ(a^(−1))F, Ψ_U⟩`, which tends to `∫ f dμ` as `a → ∞` in `H`.
6. **Theorem H.** `a_k = diag(p^k, p^(−k), 1, ..., 1)` tends to `∞` in `H`, so the orbits `V(a_k)`
   equidistribute. `SL_n(Z)` is residually finite, hence sofic, so
   `finite-equidistributed-orbits-give-sofic-action` gives soficity. ∎
