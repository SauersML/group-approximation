# SL_n(Z) on the space of unimodular lattices is sofic, part 2 (2026-09-12)

Continues `research/artifacts/sl3z-lattice-space-hecke-sofic-2026-09-12.md`, with the notation of its
Section 3: `G = SL_n(R)`, `Γ = SL_n(Z)`, `H = SL_n(Q_p)`, `K = SL_n(Z_p)`, `Δ = SL_n(Z[1/p])`,
`Y = (G × H)/Δ`, `π : Y → X_n`, and `V(a) = Γ·a^(−1)Γ`. Status: **unreviewed**.

## 4. Lemma E: Hecke orbits equidistribute

**Lemma E.** Let `a_k ∈ Δ` leave every compact subset of `H`. For every `f ∈ C_c(X_n)`,

```text
(1/|V(a_k)|) Σ_(x ∈ V(a_k)) f(x)  →  ∫ f dμ .
```

*Proof.* **Uniform continuity.** Put `ω_f(U) = sup_(u ∈ U, x ∈ X_n) |f(ux) − f(x)|`. Then
`ω_f(U) → 0` as `U` shrinks to `1`. Indeed, for `u` in a compact neighbourhood `U_0`,
`f(ux) − f(x)` vanishes unless `x ∈ U_0^(−1)·supp f`, a compact set, and `(u,x) ↦ f(ux)` is uniformly
continuous on `U_0 × U_0^(−1) supp f`.

**Thickening.** Let `U ∋ 1` be open with `U^(−1)U ∩ Γ = {1}` (`Γ` is discrete). Then `Uγ ∩ U = ∅` for
`γ ∈ Γ ∖ {1}`, so the fundamental domain `D` of Lemma S2 can be chosen with `U ⊆ D`. Let `ψ >= 0` be
continuous, supported in `U`, with `∫_G ψ = 1`, and let `ν_U` be the image of `ψ(u)du ⊗ dk` under
`(u,k) ↦ (u,k)Δ`. In the coordinates `D × K` of Lemma S2 this is the measure `ψ(u)du ⊗ dk` itself. So
`ν_U = Ψ_U m_Y` with `Ψ_U` bounded and `∫ Ψ_U dm_Y = 1`.

Put `F = f∘π ∈ L^∞(Y)`. Then `∫ F dm_Y = ∫ f dμ` by Lemma S3(2).

1. By Lemma S3(3), `∫_K f(Φ_a(k)) dk` is the average of `f` over `V(a)`.
2. Since `(u,ak) = (1,a)(u,k)`, and by Lemma S3(1),

   ```text
   ∫_Y F((1,a)y) dν_U(y) = ∫_U ψ(u) ∫_K f( π((u,1)(1,ak)Δ) ) dk du = ∫_U ψ(u) ∫_K f( u·Φ_a(k) ) dk du .
   ```

   So the quantities in 1 and 2 differ by at most `ω_f(U)`.
3. The quantity in 2 is `⟨λ(a^(−1))F, Ψ_U⟩`. Write `F = F_0 + ∫F` and `Ψ_U = Ψ_0 + 1` with
   `F_0, Ψ_0 ∈ L²_0(Y)`. `λ` preserves `L²_0` and the constants, so

   ```text
   ⟨λ(a^(−1))F, Ψ_U⟩ = ⟨λ(a^(−1))F_0, Ψ_0⟩ + ∫ F dm_Y .
   ```

   By Lemma S4 the first term tends to `0` as `a = a_k → ∞`. The limit is `∫ f dμ`.

Hence `limsup_k |avg_(V(a_k)) f − ∫ f dμ| <= ω_f(U)` for every small `U`, so the limit is `0`. ∎

## 5. Proof of Theorem H

Let `a_k = diag(p^k, p^(−k), 1, ..., 1)`. Its determinant is `1` and its entries lie in `Z[1/p]`, so
`a_k ∈ Δ`. The entry `p^(−k)` has `|p^(−k)|_p = p^k → ∞`, and compact subsets of `H` have bounded
entries, so `a_k → ∞` in `H`. By Lemma S3(3), `V_k = V(a_k)` is a finite `Γ`-orbit. By Lemma E, the
normalized counting measures on `V_k` converge to `μ` against `C_c(X_n)`.

`X_n` is second countable and locally compact, `Γ` acts by homeomorphisms preserving `μ`, and `Γ` is
residually finite (congruence quotients), hence sofic. Theorem P gives that `Γ ↷ (X_n, μ)` is sofic. ∎

## 6. Remark F: the Hecke orbits are themselves asymptotically free

Let `γ ∈ Γ` be non-scalar. Then the fraction of points of `V_k` fixed by `γ` tends to `0`. So for odd
`n`, where `SL_n(Z)` has no non-trivial scalars, the finite `Γ`-sets `V_k` are a sofic approximation
of `Γ`, and the factor `W_k` of Theorem P can be dropped. This remark is not used in Section 5.

*Proof.* Put `U_k = K ∩ a_k^(−1)Ka_k`. Since `(a_k m a_k^(−1))_(ij) = (a_i/a_j)m_(ij)`,

```text
U_k = { m ∈ K : m_21 ∈ p^(2k)Z_p ,  m_2j, m_j1 ∈ p^k Z_p  (j >= 3) }
    ⊆ W_k = { m ∈ K : m e_1 ∈ Z_p e_1 + p^k Z_p^n } .
```

Under the bijection `U_k\K → V_k` of Lemma S3(3), `Φ_a(δ^(−1)) = δa^(−1)Γ`, so `δ' ∈ Γ` acts on `U_k\K`
by `U_k k ↦ U_k kδ'^(−1)`. So `γ` fixes `U_k k` iff `kγk^(−1) ∈ U_k`, and the fixed fraction is
`m_K{k : kγk^(−1) ∈ U_k} <= m_K(A_k)`, where

```text
A_k = { k ∈ K : γ v_k ∈ Z_p v_k + p^k Z_p^n },     v_k = k^(−1) e_1 .
```

(Apply `k^(−1)`, which preserves `Z_p^n` and `p^k Z_p^n`.) The sets `A_k` decrease. If `k ∈ ∩_k A_k`,
choose `λ_k ∈ Z_p` with `γv − λ_k v ∈ p^k Z_p^n`; a convergent subsequence `λ_k → λ` gives `γv = λv`. So
`v_k` is an eigenvector of `γ`. The map `k ↦ k^(−1)e_1` pushes Haar measure on `K` to the unique
`K`-invariant probability on the primitive vectors of `Z_p^n`. `K` acts transitively there, and
normalized additive Haar measure is invariant because `det = 1`, so the two agree. Since `γ` is not
scalar, each eigenspace `ker(γ − λ)`, `λ ∈ Q_p`, lies in a hyperplane, which is additive-Haar-null.
There are at most `n` of them. So `m_K(A_k) → m_K(∩ A_k) = 0`. ∎

## 7. Model tests

1. **n = 2 calibration.** `SL_2(Z) = Z/4 *_(Z/2) Z/6` lies in Păunescu's class (Theorem 3.9), so
   `SL_2(Z) ↷ SL_2(R)/SL_2(Z)` is sofic. Theorem H agrees.
2. **The hypothesis of Theorem P fails where it must.** Let `Γ <= G` be an infranormal, non-normal
   Kazhdan pair as in Kun--Thom, with `G` residually finite. The generalized Bernoulli action
   `G ↷ ({0,1}, fair)^(G/Γ)` is continuous on a compact metrizable space and is nonsofic, so by
   Theorem P it has no equidistributed finite invariant sets. Directly: Kun--Thom, arXiv:2608.06222v3,
   p. 2, verbatim from the PDF: *"Consequently, the profinite closure of Γ contains N."* Here `N` is the
   normal closure of `Γ`. Pick `g ∈ N ∖ Γ`. A colouring `c` with finite `G`-orbit is invariant under a
   finite-index normal subgroup `M`, so it is constant on the `M`-orbits of `G/Γ`, i.e. on the fibres of
   `G/Γ → G/MΓ`. Since `g ∈ MΓ`, we get `c(gΓ) = c(Γ)`. So every finite invariant set gives measure `0`
   to the clopen set `{c(gΓ) != c(Γ)}`, which has measure `1/2`. The hypothesis fails, as the
   contrapositive requires.
3. **A real object satisfies it.** Besides Theorem H: the `N`-torsion points `(N^(−1)Z/Z)^n` of `T^n`
   are finite `SL_n(Z)`-invariant sets equidistributing to Haar measure.
4. **Not automatic.** An irrational rotation of `Z` on the circle has no finite orbits.

## 8. Consequences, limits, literature bound

1. **Refutation.** `sl3z-lattice-space-action-is-not-sofic` is false (`n = 3`). The conditional routes
   `sl3z-nonsofic-action-from-lattice-space-action` and
   `mixing-nonsofic-action-from-sl3z-lattice-space-action` require it and can never fire.
2. **Exact dictionary for SL_3(Z).** Condition 1 of `induced-actions-sofic-iff-homogeneous-action-sofic`
   now holds for `SL_3(Z) <= SL_3(R)`, so a sofic seed `Z` gives a sofic induced action
   `SL_3(R) ×_(SL_3(Z)) Z` restricted to `SL_3(Z)`. Combined with
   `howe-moore-lattice-nonsofic-action-transfers-to-mixing`, for an ergodic seed `Z` the free mixing
   action `SL_3(R) ×_(SL_3(Z)) (Z × {0,1}^(SL_3(Z)))` is sofic iff `Z` is. Induction neither creates
   nor destroys soficity. A nonsofic mixing witness for `SL_3(Z)` must therefore come from a nonsofic
   seed.
3. **Scope.** Established here: `SL_n(Z)`, all `n >= 2`. The same proof runs for other arithmetic
   lattices given strong approximation at one isotropic prime, but that import is not made, so nothing
   more is claimed.
4. **Where Hecke orbits die.** Let `Λ <= SL_3(R)` be a lattice not commensurable with any conjugate of
   `SL_3(Z)`. Any cocompact lattice qualifies, for instance `SL_1(O_D)` for a cubic division algebra `D`
   over `Q`, because commensurable lattices are both uniform or both not. Every `SL_3(Z)`-orbit in
   `SL_3(R)/Λ` is infinite. A finite orbit of `gΛ` would make `SL_3(Z) ∩ gΛg^(−1)` of finite index in
   `SL_3(Z)`, hence a lattice, hence of finite index in `gΛg^(−1)`. So `SL_3(Z)` would be commensurable
   with `gΛg^(−1)`. Conjugates must be excluded, not only commensurable lattices: for
   `Λ = gSL_3(Z)g^(−1)`, the map `xΛ ↦ xgSL_3(Z)` is an isomorphism with the action of Theorem H.
   Theorem P is structurally blind there, since an extension has finite orbits only above finite orbits.
   So `SL_3(Z) ↷ SL_3(R)/Λ` is the next explicit free mixing candidate. By the coupling `SL_3(R)` it has
   the same status as `Λ ↷ SL_3(R)/SL_3(Z)`: a lattice outside the conjugate-commensurability class of
   `SL_3(Z)`, acting on the space of unimodular lattices.

   *Correction (2026-09-13).* The first landing (05d4563791) wrote "not commensurable with `SL_3(Z)`".
   Conjugates of `SL_3(Z)` by non-commensurating elements are counterexamples to that wording.
5. **Literature bound (weak).** The downloaded texts of Păunescu (arXiv:1002.0605v5), Alpeev
   (arXiv:1706.01864), Kun--Thom (arXiv:2608.06222v3) and Furman's survey (arXiv:0901.0678) contain no
   Hecke-point or homogeneous-space soficity statement (grep for `hecke`, `periodic`,
   `homogeneous space`, `equidistrib`). The session web-search budget is exhausted. The arXiv API
   answered HTTP 429 locally and empty responses from MSI. Theorem H may be known to experts as
   folklore.
