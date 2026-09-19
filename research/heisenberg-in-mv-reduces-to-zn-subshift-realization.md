---
rg: 2
id: heisenberg-in-mv-reduces-to-zn-subshift-realization
kind: claim
title: "H_3(Z) <= mV follows once the Assouad Z^N-subshift of a Lipschitz injection is a factor of N commuting elements of mV; hosts that are products of Z-systems are exactly the product-coloured realizations"
distinct_from:
  heisenberg-group-embeds-in-wobbling-group-of-some-zn: that puts H_3 in W(Z^N) and gives no element of mV; this turns the wobbling embedding into a Z^N-subshift with zero relator cocycles and names the one missing step, a Brin-Thompson realization of that subshift.
  decidable-minimal-subshifts-are-brin-thompson-factors: that is the Z-subshift realization question, feeding Boone-Higman; this is its Z^N analogue for one specific subshift, feeding Zaremsky 2.19(c).
  aperiodic-full-groups-lift-along-factor-maps: that lifts full groups of free actions; this lifts cocycle representations whose relators have identically zero cocycle, so no freeness of the base is needed, only one free point in the extension.
  heisenberg-not-in-full-groups-of-z4-actions: that kills every Z^4-set; this is a reduction and a class description for N >= 5, not an obstruction.
artifacts:
  - research/heisenberg-in-mv-reduces-to-zn-subshift-realization-proof.md
---

**ESTABLISHED** (lane proof, elementary; not independently reviewed). A reduction and a
class description. It does not decide `heisenberg-group-embeds-in-some-brin-thompson-group`.

## Setting

- `H = H_3(Z) = ⟨a, b⟩`, `S = {a^{±1}, b^{±1}}`, `c = [a, b]`.
- `mV` acts on `C^m`, `C = {0,1}^N`. Commuting `h_1, …, h_N ∈ mV` give `h^v = h_1^{v_1} ⋯ h_N^{v_N}`
  for `v ∈ Z^N`.
- By `heisenberg-group-embeds-in-wobbling-group-of-some-zn` there are `N`, `K` and an injection
  `ι : H → Z^N` with `ι(1) = 0` and `|ι(x) − ι(x s)|_1 ≤ K` for all `x` and all `s ∈ S`. Its wobbling
  embedding is `h ↦ ĥ`, with `ĥ = ι R_h ι^{-1}` on `ι(H)`, where `R_h(x) = x h^{-1}`, and `ĥ = id`
  off `ι(H)`.
- **The Assouad configuration.** Let `A = B_K^S`, where `B_K` is the `ℓ^1`-ball of `Z^N`. Define
  `x_ι ∈ A^{Z^N}` by `x_ι(z)_s = ŝ(z) − z`. Let `X_ι` be its orbit closure under the shift
  `(σ^v ξ)(z) = ξ(z + v)`.
- **Cocycles.** For `s ∈ S` put `d_s(ξ) = ξ(0)_s`. For a word `w = s_k ⋯ s_1` (with `s_1` applied
  first) define `c_w` on `A^{Z^N}` recursively: `c_∅ = 0` and
  `c_{s w'}(ξ) = d_s(σ^{c_{w'}(ξ)} ξ) + c_{w'}(ξ)`.

## Statement

**(A) Zero relator cocycles.** For every word `w` that is trivial in `H`, including `s^{-1}s`,
`c_w ≡ 0` on `X_ι`. At the base point, `c_w(x_ι) = ŵ(0) ≠ 0` for every `w` that is nontrivial in `H`.

**(B) Lift.** Suppose `h_1, …, h_N ∈ mV` commute, `U ⊆ C^m` is clopen and invariant under every
`h_i`, and `π : U → A^{Z^N}` is continuous with `π(h_i u) = σ^{e_i} π(u)` and `π(U) ⊆ X_ι`.
Suppose also that some `u_0 ∈ U` has trivial `Z^N`-stabilizer and `π(u_0) = x_ι`. Then
`L_s(u) = h^{d_s(π u)} u` on `U`, extended by the identity off `U`, defines an injective
homomorphism `H → mV`. So `H_3(Z) ≤ mV`.

More generally, any `Z^N`-system `X` with continuous `d_s : X → Z^N` whose relator cocycles vanish
identically lifts in the same way. Injectivity needs a free point `u_0` with `c_w(π u_0) ≠ 0` for
every nontrivial `w`.

**(C) Product hosts are the product-coloured realizations.** Let `(Y_i, T_i)`, `i ≤ N`, be
aperiodic Cantor `Z`-systems. Let `Z^N` act on `Y = ∏ Y_i` coordinatewise, and let `[[Z^N ↷ Y]]` be
its topological full group. The following are equivalent.
1. `H` embeds in `[[Z^N ↷ Y]]` for some such family.
2. There are finite sets `W_i`, sequences `κ_i : Z → W_i` and maps `F_s : ∏ W_i → B_K` with the
   following property. The maps `π_s(z) = z + F_s(κ_1(z_1), …, κ_N(z_N))` are bijections of `Z^N`,
   `s ↦ π_s` defines an action of `H` on `Z^N`, and this action has a free orbit.

   These are *product-coloured realizations*. Radius-`r` windows are absorbed into the alphabets
   `W_i`.

In 2 ⇒ 1 the `Y_i` can be taken to be subshifts: the orbit closure of `κ_i` paired with a
Sturmian sequence. If each such `Y_i` is Brin–Thompson realizable, meaning a factor of some
`g_i ∈ m_iV` on a clopen invariant set, then `H ≤ (m_1 + ⋯ + m_N)V` by (B).

## Consequences

1. **The missing step for a YES** is a single realization problem: the `Z^N`-analogue of
   `decidable-minimal-subshifts-are-brin-thompson-factors`, for `X_ι` itself (a free point over `x_ι` forces `π(U) = X_ι`, since `π(U)` is closed and invariant), and for
   any Lipschitz injection `ι` into any rank. Everything else in the chain is established:
   Assouad, the zero-cocycle lift, and gluing in `mV` (reproved in Step 3 of the proof; it is the argument of
   `brin-thompson-groups-contain-full-groups-of-their-elements` with `h^v` in place of `g^n`).
   - Necessary condition: `π(U)` has decidable language, by the box computation of item 1 of that
     node, run over finite windows `F ⊆ Z^N`.
2. **All product hosts form one class.** This covers the product-shift full groups
   `[[Z^N ↷ ({0,1}^Z)^N]] ≤ 2N·V`, products of realizable `Z`-systems such as SMART traces, and
   every host built by running `N` one-dimensional devices in separate coordinate blocks of `mV`.
   Each of these gives only product-coloured realizations.
   - A kill needs the same invariant for all of them: the move of the point depends on `N`
     *separate* colourings `κ_i(z_i)`.
   - For `N ≤ 4` the class is empty, by `heisenberg-not-in-full-groups-of-z4-actions`. That result
     does not use the product structure.
   - A NO for the full target must additionally handle Z^N-actions by commuting elements of mV that
     are not products. Examples are several commuting reversible machines on one tape.
3. **Where the direct attempts die.** Write `x^α y^β c^μ` in normal form. Right multiplication by
   `a` sends the `c`-orbit ("string") of the coset `(α, β)` to that of `(α+1, β)`, with the string
   parameter shifted by `−β`.
   - In a product-coloured realization, this unbounded shift must be read from `N` separate
     colourings.
   - Every encoding tried in lane w15-z-follow puts the counter `β` in coordinate positions:
     base-`b` digits, boustrophedon, homogeneous `μ/ρ` scaling, diagonal dependence. Each dies at
     this step, because the move in coordinate `i` depends on `z_j`, `j ≠ i`, only through
     `κ_j(z_j)`.
   - These are failed constructions, not a proof that the class is empty.

**Proof.** `research/heisenberg-in-mv-reduces-to-zn-subshift-realization-proof.md`.
