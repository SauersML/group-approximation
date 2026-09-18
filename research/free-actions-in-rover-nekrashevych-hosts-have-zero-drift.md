---
rg: 2
id: free-actions-in-rover-nekrashevych-hosts-have-zero-drift
kind: claim
title: In a Röver–Nekrashevych group V_d(K), an element with nonzero mean depth drift for some invariant measure has an attracting periodic point, and a finitely generated subgroup whose drift cocycle is a continuous coboundary embeds in S_n ≀ K; so for contracting K a free group acting freely needs a non-coboundary drift cocycle with zero drift for every element
requires:
  - exponential-growth-groups-admit-no-contracting-block-hierarchies
  - v-times-inflation-host-full-groups-are-finitely-presented
distinct_from:
  exponential-growth-groups-admit-no-contracting-block-hierarchies: that excludes geometric (group-metric) hierarchies over exponential-growth groups; this addresses the remaining fibre-type option, namely finite-state free actions inside contracting hosts, and reduces it for Röver–Nekrashevych hosts to one cocycle condition.
  contracting-rover-nekrashevych-groups-are-f-infinity: that concerns finiteness properties of V_d(G) for contracting G; this concerns which subgroups of V_d(K) can act freely.
---

**Partial answer** (lane bh-invent-06b, 2026-09-18) to the question "can a contracting RSG contain a free group
acting freely?", for the synchronous class `V_d(K)`. Elementary lane proof, not reviewed. It uses Birkhoff and
Poincaré recurrence, and Nekrashevych's theorem that contracting self-similar groups contain no free subgroups
(*Free subgroups in groups acting on rooted trees*, GGD 2010; recalled, not re-read). No priority is claimed.

## Setting

- `K ≤ Aut(T_d)` is self-similar, and `G = V_d(K)` is its Röver–Nekrashevych group acting on `∂T_d = {0..d−1}^ℕ`.
  Every `g ∈ G` has a cone partition `{C_(α_i)}` with `g(α_i w) = β_i k_i(w)`, `k_i ∈ K`.
- The **drift** is `δ_g(x) = |β_i| − |α_i|` for `x ∈ C_(α_i)`. It is locally constant and satisfies the cocycle
  identity `δ_(gh)(x) = δ_g(hx) + δ_h(x)`. Write `Δ_n(x) = δ_(g^n)(x)`.
- There is `L_g` such that for every cone `C_γ` with `|γ| >= L_g`, `g(C_γ)` is the cone of depth
  `|γ| + δ_g` around `g(x)`, and `g|_(C_γ) = L_(g_*γ) ∘ k ∘ L_γ^(−1)` with `k ∈ K`. The local actions are in `K`
  because `K` is self-similar.

## Statement

1. **Nonzero drift gives periodic points.** If some `g`-invariant probability measure `ν` has `∫ δ_g dν ≠ 0`,
   then `g` has a periodic point, and a power of `g` maps a cone strictly into itself.
2. **Free actions are drift-free.** If `H ≤ G` acts freely, every `h ∈ H \ {1}` has `∫ δ_h dν = 0` for every
   `h`-invariant `ν`.
3. **Coboundary drift gives a wreath embedding.** Let `H ≤ G` be finitely generated, and suppose
   `δ_h(x) = f(hx) − f(x)` for a continuous `f : ∂T_d → Z` and all `h ∈ H`. Then `H` embeds in `S_n ⋉ K^n` for
   some `n`. If `K` is contracting, then `H` contains no free subgroup of rank 2.
4. **Exact residue.** For contracting `K`, a subgroup `F_2 ≅ H ≤ V_d(K)` acting freely on `∂T_d` must have a drift
   cocycle that is **not** a continuous coboundary, while **every single element** has zero drift. Whether such
   an `H` exists is the whole of the question for Röver–Nekrashevych hosts.

## Proof

**1.**
- Pass to an ergodic component, and replace `g` by `g^(−1)` if needed. So `∫ δ_g dν = c > 0`.
- For `ν`-almost every `x`, Birkhoff gives `Δ_n(x)/n → c`, and Poincaré gives recurrence. Fix such an `x`. Then
  `M := −min_(j >= 0) Δ_j(x)` is finite.
- Let `m >= L_g + M`. Inductively, `g^j(C_(x|m))` is the cone of depth `m + Δ_j(x) >= L_g` around `g^j x`, and
  `g^j` acts on it by prefix replacement composed with an element of `K`.
- By recurrence choose `n` with `g^n x ∈ C_(x|m)` and `Δ_n(x) >= 1`. Then `g^n(C_(x|m))` is a cone of depth
  `m + Δ_n > m` inside `C_(x|m)`.
- The map `g^n|_(C_(x|m))` is a prefix lengthening composed with a tree automorphism, which is an isometry. In the
  standard ultrametric it is therefore a strict contraction, and it has a fixed point. ∎

**2.** A free action has no periodic points for elements of infinite order, and torsion elements have zero drift.
Apply item 1. ∎

**3.**
- Let `S` generate `H`. Choose `D` so that every cone `C_γ` with `|γ| − f = D` on `C_γ` has three properties: it
  lies inside a level set of `f`; it lies inside a piece of every `s ∈ S^(±1)`; and `|γ| >= L_s`.
- Let `𝒞_D` be the set of cones around each `x` of depth `D + f(x)`. This is a finite clopen partition, since `f`
  is locally constant.
- Each `s` maps a cone of depth `D + f(x)` to a cone of depth `D + f(x) + δ_s(x) = D + f(sx)` around `sx`. So `s`
  permutes `𝒞_D`, and on each cone it acts, via canonical similarities, by an element of `K`.
- Hence all of `H` does, and `h ↦ (permutation of 𝒞_D, K-labels)` is a homomorphism `H → S_n ⋉ K^n`,
  `n = |𝒞_D|`. It is injective because it determines the action.
- A finite-index subgroup of `H` embeds in `K^n`. If `F_2 ≤ K^n`, the kernels of the two coordinate projections
  (for `K^n = K × K^(n−1)`) are commuting normal subgroups of `F_2` with trivial intersection. In `F_2` one of them
  must be trivial, so by induction `F_2` embeds in `K`. For contracting `K` that is impossible. ∎

**4.** Items 2 and 3. ∎

## Instances

- **`K = 1`** (Higman–Thompson `V_d`). Every infinite-order element has attracting periodic points (revealing
  pairs, Salazar-Díaz; recalled, not re-read). So no infinite-order element of `V_d` acts freely, which is
  consistent with item 3, since here `K^n` is trivial. The case of finite nontrivial `K` is not treated.
- **`K` = the adding machine.** This is the host of part A of `v-times-inflation-host-full-groups-are-finitely-presented`.
  Fixed-point-free elements of infinite order exist (the odometer). Free subgroups acting freely are open exactly
  in the form of item 4.

## Lesson for general BH

Keeping freeness in Track A while compressing in a fibre needs a free group acting freely by finite-state maps
inside a contracting host.
- **What synchronous hosts force.** Every element of such an action must be drift-free (item 1: a drifting
  element has an attracting cone, hence a periodic point).
- **Why the drift must be genuinely twisted.** If the drift is untwisted, meaning a coboundary, the whole group
  collapses into a finite wreath product over the units, which has no free subgroups when the units are
  contracting.
- **The remaining object is sharp:** a free group in `V_d(K)` whose depth cocycle has zero drift for every element
  but is not a coboundary. No such object is known.

So free Track A with fibre compression stands or falls with this cocycle problem. Otherwise it must accept isotropy
(E3′).
