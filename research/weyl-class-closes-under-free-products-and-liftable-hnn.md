---
rg: 2
id: weyl-class-closes-under-free-products-and-liftable-hnn
kind: claim
title: "The F_m-Weyl class is closed under free products and under HNN extensions and amalgams whose associated subgroups lift to type F_m extensions of Sigma compatibly with Sigma; the lift forces type F_m associated subgroups and a matching outer action, so Higman's construction does not run through it"
distinct_from:
  normalized-benign-witnesses-give-the-semidirect-join: That defines the F_m-Weyl class, proves it contains type F_m groups and quotients Gamma/M and is closed under subgroups and direct products, and shows U Weyl implies (d) and the root; this proves closure under free products and liftable HNN extensions and amalgams, and isolates the two lifting conditions that stop Higman's construction.
  u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples: That is an obstruction to any Weyl pair for U through the outer action on Sigma; this is the positive closure theory whose HNN step needs that same outer action to match.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Fix
`m ∈ {2, ..., ∞}` or `m = F`. A **Weyl pair** is `Σ ≤ Λ` with `Σ, Λ` of type
`F_m`; put `M = N_Λ(Σ)`, `W = M/Σ`, and let `ρ : W -> Out(Σ)` be the outer
action. A group is **`F_m`-Weyl** if it embeds in such a `W`
(`normalized-benign-witnesses-give-the-semidirect-join`, item 2).

1. **Free products.** If `G_i ≤ M_i/Σ_i` for Weyl pairs `(Λ_i, Σ_i)`,
   `i = 1, 2`, then `G_1 * G_2` is `F_m`-Weyl, with the Weyl pair
   `Λ = (Λ_1 × Σ_2) *_{Σ_1 × Σ_2} (Σ_1 × Λ_2)`, `Σ = Σ_1 × Σ_2`. Indeed
   `N_Λ(Σ) ⊇ (M_1 × Σ_2) *_Σ (Σ_1 × M_2)`, and modulo `Σ` this is
   `(M_1/Σ_1) * (M_2/Σ_2)`.
   - First test: `G` Weyl ⇒ `G * Z` Weyl. Directly, one can use
     `Λ *_Σ (Σ × Z)`, where the new letter centralizes `Σ`.
   - Hence `G * H` is Weyl for every type `F_m` group `H` and every finite
     `H`.
2. **Liftable HNN extensions.** Let `G ≤ W`, let `φ : C_1 -> C_2` be an
   isomorphism of subgroups of `G`, and call `φ` **liftable** if there are
   type `F_m` subgroups `Σ ≤ A, B ≤ M` with `A/Σ = C_1`, `B/Σ = C_2` and an
   isomorphism `θ : A -> B` with `θ(Σ) = Σ` inducing `φ`.
   - Then `Λ' = Λ *_θ` is of type `F_m`, its stable letter `t` normalizes `Σ`,
     `<M, t> = M *_θ`, and `<M, t>/Σ = W *_φ̄ ⊇ G *_φ`.
   - So the HNN extension `G *_φ` is `F_m`-Weyl.
3. **Liftable amalgams.** For `G_1 *_C G_2`, with `C_i ≤ G_i` and
   `φ : C_1 -> C_2` liftable in the free-product pair of item 1, the amalgam
   is `F_m`-Weyl. It embeds in the HNN extension `(G_1 * G_2) *_φ`.
4. **What a lift costs.** If `φ` is liftable along `(Λ, Σ)`:
   - **(a) Finiteness.** `C_1 = A/Σ` and `C_2 = B/Σ` are of type `F_m`, since
     a quotient of a type `F_m` group by a type `F_{m-1}` normal subgroup is
     of type `F_m`. For `m = F` they are of type `F_∞`, with torsion allowed.
   - **(b) Outer action.** `ρ(φ(c)) = τ ρ(c) τ^{-1}` for all `c ∈ C_1`,
     where `τ ∈ Out(Σ)` is the class of `θ|_Σ`.
   - (b) is necessary for every construction that keeps `Σ`. If `t` lies in
     any group containing `Λ`, normalizes `Σ`, and conjugates a lift of each
     `c ∈ C_1` into the coset of a lift of `φ(c)`, then (b) holds with
     `τ = [conj(t)|_Σ]`.
   - (a) is necessary for the HNN presentation of item 2 to be of type
     `F_m`: the associated subgroups must be of type `F_m`.
5. **Consequence for Higman's construction.** The HNN steps of Higman's
   embedding identify finitely generated subgroups `L` of finitely presented
   groups (the benign witnesses of the classical proof). By 4(a), each step
   is liftable only if its associated subgroups are realized as `A/Σ` with
   `A` of type `F_m`. That is the type `F_m` benign statement for those
   subgroups. So running Higman's construction through item 2 reproduces the
   root; it does not bypass it.
   - If `U` is `F_m`-Weyl, then the Weyl class is closed under HNN
     extensions along arbitrary finitely generated subgroups of its finitely
     generated members.
   - Reason: finitely generated subgroups of a Weyl group are recursively
     presented. A word lies in the kernel iff its lift lies in the finitely
     generated `Σ`, which is r.e. So such an HNN extension embeds in `U`.
   - Thus the unrestricted closure is a consequence of the target, not a
     tool towards it.

So closure of the Weyl class holds in the form "free products, and liftable HNN
extensions and amalgams". The unrestricted HNN step fails for the lifting
method at exactly two places: the finiteness 4(a), which is benignness
again, and the outer-action match 4(b). The companion obstruction
`u-weyl-pairs-need-out-sigma-to-contain-all-finite-simples` shows
that 4(b) is a real constraint for `U`: `ρ` must be injective on every
nonabelian finite simple subgroup.

Proof: route `weyl-class-closes-under-free-products-and-liftable-hnn-proof`.
