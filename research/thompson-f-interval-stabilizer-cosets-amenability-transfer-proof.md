---
rg: 2
id: thompson-f-interval-stabilizer-cosets-amenability-transfer-proof
kind: route
title: Invariant means on stretched restrictions push forward to almost invariant measures on F through a scale-equivariant extension
target: thompson-f-interval-stabilizer-cosets-separate-only-if-amenable
requires:
  - thompson-f-following-models-separate-iff-mean-charges-commutator
artifacts:
  - research/artifacts/thompson-f-nonspatial-f-sets-2026-09-13.md
---

Notation:
- `Σ = {x_0^±1, x_1^±1}`;
- `P` is the set of finitely supported probability measures;
- `||·||` is the `ℓ1` norm.

**0. Transfer lemma.**
- **Setting.** `m` is an invariant mean on an `F`-set `Ω`, and `U_* ⊆ U ⊆ Ω`.
  - `m(U_*) = κ > 0`, and for each `s ∈ Σ`, `sU_* ⊆ U` and `m(sU_* Δ U_*) = 0`.
  - `Φ : U → F` is injective with `Φ(sω) = sΦ(ω)` for `ω ∈ U_*` and `s ∈ Σ`.
- **Conclusion.** `F` is amenable.
- **Almost invariant measure.** Steps 2.1–2.3 of
  `thompson-f-following-models-mean-charges-commutator-proof` apply. The conditions `μ(U_*) > κ - η`
  and `μ(sU_* Δ U_*) < η` are weak*-open and hold at `m`. So for every `η > 0` some `μ ∈ P` satisfies
  them and has `||sμ - μ|| < η` for `s ∈ Σ`.
- **Restrict.** Put `μ_* = μ·1_(U_*)`. Then `sμ_* = (sμ)·1_(sU_*)`, so
  `||sμ_* - μ_*|| ≤ ||sμ - μ|| + μ(sU_* Δ U_*) < 2η`.
- **Push forward.** Put `ν = Φ_*μ_*`.
  - `Φ(sω) = sΦ(ω)` on `U_*` gives `sν = Φ_*(sμ_*)`.
  - `Φ` is injective on `U`, which carries both measures, so `||sν - ν|| = ||sμ_* - μ_*|| < 2η`.
  - `||ν|| > κ - η`.
- **Conclude.** Normalizing gives finitely supported probability measures on `F` that are
  `2η/(κ-η)`-invariant under `Σ`. A weak*-cluster point as `η → 0` is an invariant mean on `F`, as in
  step 1 of the companion route. So `F` is amenable.

**1. Finite Z.**
- For `e ∈ Z`, `p_e(f|_Z) = f(e)` is equivariant.
- `c` moves `f|_Z` only if it moves some `f(e)`, and `c` fixes `[0,1/4] ∪ [3/4,1]` pointwise.
- So `Moved(c) ⊆ ∪_e p_e^-1[1/4,3/4]`, which is null by item 4 of the companion claim.

**2. Z with interior.**
1. **Endpoints.** List the endpoints of the components of `Z` as `0 = e_0 < e_1 < ... < e_M = 1`,
   counting an isolated point once. Each `[e_j, e_(j+1)]` is either a component interval of `Z`, or the
   closure of a gap, a component of `[0,1] \ Z`.
2. **Null slabs.** For `y ∈ (0,1/2)` let `N_y = {φ : φ(e_j) ∈ [y, 1-y] for some j}`. It is null by
   item 4 of the companion claim, applied to `p_j(φ) = φ(e_j)`.
3. **Where Moved(c) lives.** For a component interval `I = [e_l, e_r]` of `Z`, let
   `W_I^y = {φ : φ(e_l) < y, φ(e_r) > 1 - y}`.
   - Take `φ ∉ N_y` with `y ≤ 1/4`. `φ` is increasing, so exactly one `j` has `φ(e_j) < y` and
     `φ(e_(j+1)) > 1 - y`.
   - If `[e_j, e_(j+1)]` is a gap, then `φ(Z) ⊆ [0,y) ∪ (1-y,1]`, where `c` is the identity, and `c`
     fixes `φ`. So `Moved(c) \ N_y ⊆ ∪_I W_I^y`.
   - If `m(Moved(c)) > 0`, some `I` has `m(W_I^(1/4)) > 0`. Then `m(W_I^(1/16)) > 0`, because
     `W_I^(1/4) \ W_I^(1/16) ⊆ N_(1/16)`.
4. **The generators near the ends.** On `[0,1/4]` each `s ∈ Σ` is `u ↦ 2^k u`, and on `[7/8,1]` it is
   `u ↦ 1 - 2^(k')(1 - u)`, with `k, k' ∈ {-1,0,1}`:
   - `x_0 = u/2` on `[0,1/2]` and `2u - 1` on `[3/4,1]`;
   - `x_0^-1 = 2u` on `[0,1/4]` and `(u+1)/2` on `[1/2,1]`;
   - `x_1` and `x_1^-1` are the identity on `[0,1/2]`;
   - `x_1 = 2u - 1` on `[7/8,1]`, and `x_1^-1 = (u+1)/2` on `[3/4,1]`.
5. **The extension.** Put `U = W_I^(1/8)` and `U_* = W_I^(1/16)`. For `φ = f|_Z ∈ U`:
   - **Left gaps** lie left of `e_l`, so their endpoint images lie in `[0,1/8)`.
     - If `e_l > 0`, let `n` be the integer with `2^n φ(e_l) ∈ [1/4, 1/2)`.
     - For a left gap `G = (e_i, e_(i+1))`, the pair `(u,v) = (2^n φ(e_i), 2^n φ(e_(i+1)))` is realized
       by `2^n f` on `[e_i, e_(i+1)]`, which is piecewise linear with dyadic breakpoints and
       power-of-2 slopes.
     - Fix one such map `ψ_(G,u,v) : [e_i, e_(i+1)] → [u,v]` for each triple that occurs, and set
       `Φ(φ) = 2^-n ψ_(G,u,v)` on `G`.
   - **Right gaps** are handled symmetrically.
     - `n'` normalizes `1 - φ(e_r)` into `[1/4,1/2)`.
     - `(u',v')` are the normalized images measured from 1, and on each right gap `G`,
       `Φ(φ) = 1 - 2^(-n')(1 - ψ'_(G,u',v'))`.
   - **On `Z`,** `Φ(φ) = φ`.

   So `Φ(φ) ∈ F`: it is continuous at every `e_j`, piecewise linear with dyadic breakpoints (the `e_j`
   are dyadic), and has power-of-2 slopes. It restricts to `φ` on `Z`, so `Φ` is injective.
6. **Equivariance.** Let `φ ∈ U_*` and `s ∈ Σ`.
   - All left images lie in `[0,1/16)` and all right images in `(15/16,1]`, where `s` is a scaling by
     step 4. So `sφ ∈ U`.
   - The left normalization of `sφ` is `n - k`, and the normalized pairs are unchanged. So on left
     gaps `Φ(sφ) = 2^(-(n-k)) ψ = s ∘ 2^-n ψ`.
   - The same holds on right gaps, and on `Z` both sides equal `s ∘ φ`. So `Φ(sφ) = sΦ(φ)`.
7. **Almost invariance.** `s` changes each end image by a factor at most 2, so
   `sU_* Δ U_* ⊆ N_(1/32)`, which is null. The transfer lemma gives amenability of `F`.

**3. Amenable H** (standard).
- Let `λ` be a left-invariant mean on `H`.
- For `f ∈ ℓ∞(F)` put `f̃(gH) = λ(h ↦ f(gh))`. This does not depend on the representative: replacing
  `g` by `gh_0` left-translates the argument by `h_0`.
- Left translation of `f` by `k` sends `f̃` to its translate by `k`.
- So if `m` is an invariant mean on `F/H`, `M(f) = m(f̃)` is a left-invariant mean on `F`.
