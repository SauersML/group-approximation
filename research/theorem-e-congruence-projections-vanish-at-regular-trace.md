---
rg: 2
id: theorem-e-congruence-projections-vanish-at-regular-trace
kind: claim
title: At the regular trace, congruence-kernel fixed and almost-invariant subspaces of the Theorem E vertex have zero mass at every fixed level
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1) itself, open; this shows the congruence-kernel projection route to it has zero mass at every fixed level and can only work at escaping levels.
  laurent-extension-agrees-iff-inverse-defects-commute: that is an extension criterion whose item 3 notes that the unit order of x_i is unbounded; this shows that roundings escape every nonzero ring element and every fixed congruence level, with vanishing fixed and almost-invariant mass.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is Becker--Lubotzky's exclusion of strict stability; this is a trace computation bounding what a congruence-kernel projection can capture, and it leaves flexible stability open.
  uniform-kazhdan-fails-for-linear-theorem-e-pair: that is the literature fact that Kazhdan constants degrade across generating sets; this proves fixed-level almost-invariant subspaces have vanishing dimension, so correction at a fixed level has nothing to act on.
artifacts:
  - research/artifacts/nh-h1-theorem-e-instance-2026-09-12.md
---

**ESTABLISHED.** Setting:
- `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, with `r, d >= 3`.
- `σ : G -> U(∏_U M_n)` is trace-preserving, i.e. `τ∘σ = δ_e`. Only `τ∘σ|Γ = δ_e` is used.
- `Γ(I)` is the principal congruence kernel of a finite-index ideal `I`. It is infinite, since it contains `e_12(I)`.

1. **Fixed vectors.**
   - For every infinite `K ≤ Γ`, the largest projection fixed by `σ(K)` has trace 0.
   - In coordinates, projections `p_n` that are `ε`-almost fixed by `m` distinct elements satisfy
     `lim_U tr p_n <= 1/(m(1-ε)^2)`.
   - Hence `p_prof = ∨_I p_(Γ(I))` has trace 0.
2. **Almost-invariant vectors.**
   - Let `S` be finite and symmetric with `ℓ^2`-Kazhdan constant `κ`, for example a Kazhdan pair of `Γ(I)`.
   - Subspaces on which `σ_n` is `ε`-almost invariant under `S`, with `ε < κ/√|S|`, have `lim_U dim/n = 0`.
   - Proof: the spectral measure of `Σ_(s∈S) Re σ(s)/|S|` equals that of `λ_Γ`, and it has no mass above
     `1 - κ^2/(2|S|)`.
3. **Profinite models.**
   - For an arbitrary model, `τ(p_prof) = 1` implies (H1), because finite groups are HS-stable.
   - So the fixed-subspace route proves (H1) exactly for purely profinite vertex restrictions, and at the regular
     trace there are none.
4. **Roundings.** If `π_n` are (H1) roundings of `σ|Γ`:
   - `tr π_n(g) -> δ_e(g)` along `U`;
   - `{n : π_n(g) = 1} ∉ U` for every `g ≠ e`;
   - `π_n(Γ(I))`-fixed mass tends to 0 for every fixed `I`;
   - the root ideals `I_n` satisfy `{n : f ∈ I_n} ∉ U` for every `f ≠ 0`.

   A correction at levels `Γ(I_n)` must use generating sets of `F`-length `>= ρ_n -> ∞`, and there the Kazhdan
   constants are not uniform (`uniform-kazhdan-fails-for-linear-theorem-e-pair`).

**Consequence for (H1).**
- The candidate route has zero mass at every fixed level: almost-invariant vectors of congruence kernels, projection
  onto fixed subspaces, then Kazhdan correction.
- The hard step "almost-invariant but not close to invariant" does not arise at a fixed level: the
  almost-invariant subspace itself is asymptotically empty.
- Content can live only at `n`-dependent escaping levels, on words of unbounded length.
- Extendability to `G` shortens the normal generators of the level `(x_1^m..x_d^m)` to `G`-length `O(log m)`.
  Averaging over the quotient needs `G`-length `>= m^d log q / log(2|F_G|+1)` (artifact Remark 4, counting bound
  proved, distortion bound imported).
- `hs-stable-vertex-rounding-for-every-model` stays OPEN.
