---
rg: 2
id: kt-gamma-saturation-is-gamma-or-contains-e
kind: claim
title: For the Theorem E pair the bicommutant saturation of Gamma in any representation is Gamma or contains E, so the hyperlinear floor is Gamma or E
distinct_from:
  kt-compressor-commutant-collapse-is-all-or-nothing: that proves the wall alternative, in which the saturation meets each root group in its polynomial part; this proves that in a wall the saturation is exactly Gamma, with no non-root elements of E or of G outside Gamma
  kt-hyperlinear-floor-is-root-invisible-laurent-overgroup: that leaves a third alternative, a root-invisible Laurent overgroup strictly between Gamma and E; this shows that alternative is empty, both for the floor K_Gamma and model by model
  kt-compressor-stable-kernel-overgroups-are-polynomial: that is the group-theoretic sandwich for Mon-stable subgroups of SL_r(R); this applies it to the saturations of arbitrary representations and handles the SL_d(Z) part of the saturation
  kt-pair-hyperlinear-floor-below-normal-closure: that is the open existence question for a hyperlinear floor below E; this proves it is equivalent to hyperlinear W_Gamma, and gives the single-enemy criterion
---

**ESTABLISHED (proposed; proof in `kt-gamma-saturation-zero-one-law-proof`).**
Let `q` be a prime power, `r,d ≥ 3`, `R_+ = F_q[x_1,…,x_d]`, `R = F_q[x_1^(±1),…,x_d^(±1)]`,
`E = EL_r(R)`, `Γ = EL_r(R_+)`, `G = E ⋊ SL_d(Z)` (Kun--Thom Theorem E). Let `U` be **any**
group and `π : G → U` **any** homomorphism. Put `C_0 = C_U(π(Γ))` and

```text
Γ^sat(π) = { g ∈ G : π(g) commutes with C_0 } = π^(-1)( C_U(C_U(π(Γ))) ).
```

**Theorem (saturation zero-one law).** Either `E ≤ Γ^sat(π)`, or `Γ^sat(π) = Γ`.

For `U = U(M)`, `M` a von Neumann algebra, `C_0` spans `π(Γ)' ∩ M`, so the dichotomy reads:
either `π(E)` commutes with `π(Γ)' ∩ M`, or the only `g ∈ G` with `π(g) ∈ (π(Γ)' ∩ M)'` are the
elements of `Γ`.

## Corollaries

1. **The floor is all or nothing.** The least scalar-RE overgroup `K_Γ`
   (`kt-hyperlinear-floor-is-root-invisible-laurent-overgroup`) is `Γ` or `E`. Alternative 3
   of that trichotomy (a root-invisible Laurent overgroup) does not occur.
2. **The floor node is the wreath model.** `kt-pair-hyperlinear-floor-below-normal-closure`
   holds iff `W_Γ` is hyperlinear (`hyperlinear-wreath-model` for this pair). The Theorem-C
   route to a hyperlinear nonsofic action gives no discount at this pair.
3. **One enemy suffices.** `W_Γ` is hyperlinear iff some canonical CE actor model
   `σ : G → U(M)` of `G` has one element of `σ(Γ)' ∩ M` that does not commute with the single
   unitary `σ(e_12(x_1^(-1)))`. That model then separates **every** `g ∈ G ∖ Γ` from `Γ` by a
   `Γ`-central projection, so it alone certifies scalar relative embeddability of
   `L(Γ) ≤ L(G)`. No family of models and no joint moment condition is needed.
4. **Weak target equals strong target.** `W_Γ` is non-hyperlinear iff one element
   `h ∈ E ∖ Γ` lies in `K_Γ`, iff all of `E` does, iff (CCR) holds for every compressor in
   every canonical CE actor model. A witness of any shape (not only a root or a torus) already
   forces the full collapse.

## What this kills

Every candidate intermediate subgroup `Δ` with `Γ < Δ` and `E ⊄ Δ`, compressor-stable or not,
split or not, has `W_Δ` hyperlinear only if `W_Γ` is. The search for a hyperlinear floor below
the normal closure is the search for a hyperlinear `W_Γ`, and nothing else.
