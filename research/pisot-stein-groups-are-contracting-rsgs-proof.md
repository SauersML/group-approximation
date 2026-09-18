---
rg: 2
id: pisot-stein-groups-are-contracting-rsgs-proof
kind: route
title: Local actions of Pisot-slope piecewise-affine maps on the β-shift have bounded slope defect and bounded-conjugate offsets, hence a finite nucleus
target: pisot-stein-groups-are-contracting-rsgs
requires: [contracting-rsgs-embed-in-fp-simple-groups]
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

Notation:
- `len(z)` is the length of the finite greedy expansion of `z ∈ Z[β] ∩ [0,1)`, which exists by (F).
- `σ` ranges over the embeddings of `Q(β)` other than the identity, and `ρ_σ := |σ(β)| < 1`.
- `D := ⌊β⌋` is the largest digit.

1. **Coding.**
   - Admissible words `u` give cylinders `[u] ⊆ X_β`. Their images are half-open intervals
     `I_u = [a_u, a_u + β^{-|u|} ℓ_{t(u)})`, where `a_u = Σ u_i β^{-i}` and `ℓ_v ∈ Z[β] ∩ (0,1]` is the length
     of the follower interval of the state `v`. There are finitely many states.
   - The level-`n` intervals partition `[0,1)`, and their left endpoints are exactly the `z` with `len(z) ≤ n`.
   - Two admissible sequences have the same value iff it is such an endpoint. So `π` is an order-preserving
     homeomorphism from `X_β` onto `[0,1)` Cantorized at `Fin(β) = Z[β] ∩ [0,1)`, using (F).
   - Elements of `V_β` are piecewise increasing affine maps `x ↦ β^k x + c`, with `c ∈ Z[β]` and breakpoints in
     `Z[β]`. So they are homeomorphisms of `X_β` (Tanner's realization).
   - A cone-to-cone canonical similarity `[u] → [u']` with `t(u) = t(u')` is
     `x ↦ a_{u'} + β^{|u|−|u'|}(x − a_u)`. So `V_{X_β} ≤ V_β`, and `V_β` is an RSG by BBMZ Prop. `RSGsAndV`,
     once it is known to consist of rational maps.
2. **Length lemma.**
   - **Claim.** For every `C` there is `L(C)` such that: if `z ∈ Z[β] ∩ [0,1)`, `n ∈ Z`, and
     `|σ(z)| ≤ C ρ_σ^{−n}` for all `σ`, then `len(z) ≤ n + L(C)`.
   - **Proof.** Put `y = β^n z ≥ 0`, so `|σ(y)| ≤ C`.
     - The greedy expansion of `y` is that of `z` shifted by `n`. Write it as integer part
       `I = Σ_{j≥0} y_j β^j ∈ Z[β]` plus fractional part `F = y − I ∈ Z[β] ∩ [0,1)`.
     - `|σ(I)| ≤ D/(1−ρ_σ)`, so `|σ(F)| ≤ C + D/(1−ρ_σ)`.
     - Elements of `Z[β]` with all absolute values bounded form a finite set, because `β` is Pisot and
       `Z[β]` is a lattice in Minkowski space. So `F` ranges over a finite set, each element of which has
       finite length by (F).
     - `len(z) = n + len(F)` when `len(z) > n`. ∎
   - **Also.** If `len(b) ≤ L`, then `|σ(b)| ≤ D ρ_σ^{−L}/(1−ρ_σ)`.
3. **Slope defect.** Fix `f ∈ V_β`. Let `[w]` be a cone deep enough to lie in one affine piece `x ↦ β^k x + c`,
   and put `J = f(I_w)`, of natural level `|w| − k`.
   - **Suppose `J` straddles a boundary.** That is, some `b` with `len(b) ≤ L` lies in the interior of `J`.
     Then `p = β^{−k}(b − c)` lies in the interior of `I_w`, so `len(p) > |w|`.
   - **Coarse boundaries.** Only finitely many `b` have `len(b) < L_0(c)`, where `L_0(c)` is the least `L` with
     `ρ_σ^L |σ(c)| ≤ 1` for all `σ`. Their preimages are finitely many points of finite length, so they are
     interior to no cone of large level.
   - **Fine boundaries.** For `L ≥ L_0(c)`,
     `|σ(p)| ≤ ρ_σ^{−k}(D ρ_σ^{−L}/(1−ρ_σ) + |σ(c)|) ≤ C_β ρ_σ^{−(k+L)}`,
     with `C_β := max_σ D/(1−ρ_σ) + 1`. By step 2, `len(p) ≤ k + L + L_β`, where `L_β := L(C_β)` depends only
     on `β`. Hence `L > |w| − k − L_β`.
   - **Conclusion.** For `|w| ≥ N(f)`, `J` lies in a single cylinder of level `|w| − k − L_β`, so the smallest
     cone `ō(w)` containing `f([w])` satisfies `|ō(w)| ≥ |w| − k − L_β`.
     - Comparing lengths also gives `|ō(w)| ≤ |w| − k + log_β(ℓ_max/ℓ_min)`.
     - So the local slope exponent `e := k + |ō(w)| − |w|` lies in a fixed finite interval
       `[−L_β, log_β(ℓ_max/ℓ_min)]`, independent of `f`.
4. **Offsets.** The local action is `π(f|_w(ω)) = d + β^e π(ω)` with `d = β^{|ō(w)|}(β^k a_w + c − a_{ō(w)})`.
   - It lies in `Z[β] ∩ [0, ℓ_max)`.
   - By step 2's estimate,
     `|σ(d)| ≤ D/(1−ρ_σ)·(ρ_σ^{e} + 1) + ρ_σ^{|ō(w)|}|σ(c)| ≤ D/(1−ρ_σ)·(ρ_σ^{−L_β} + 1) + 1`
     for `|w|` large.
   - So `d` ranges over a finite set independent of `f`.
5. **Finite nucleus.** A local action at a deep cone is determined by
   `(t(w), t(ō(w)), e, d)`, which ranges over a finite set `𝒩`.
   - So every `f` has finitely many local actions, and is rational, since the shallow cones are finitely many.
   - Every deep local action lies in `𝒩`, so `Nuc_{V_β} ⊆ 𝒩` is finite.
   - `X_β` is an irreducible SFT, so `V_β` is a contracting RSG containing `V_{X_β}`. By
     `contracting-rsgs-embed-in-fp-simple-groups`, it and all its subgroups embed in finitely presented simple
     groups.
6. **Other lengths.** Pick `m` with `β^{−m}ℓ ≤ 1`. Conjugating by `x ↦ β^{−m}x` and extending by the identity on
   `[β^{−m}ℓ, 1)` embeds `V(Z[β],⟨β⟩,ℓ)` in `V_β`, since slopes and breakpoints stay in `⟨β⟩` and `Z[β]`. ∎
