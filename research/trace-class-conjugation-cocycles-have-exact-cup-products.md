---
rg: 2
id: trace-class-conjugation-cocycles-have-exact-cup-products
kind: claim
title: "Class-kill for (K), operator-algebra models: if b_1 = U F U^* - F has a bounded (or S_p) potential F and b_2 takes trace-class (S_p') values in the conjugation representation on Hilbert-Schmidt operators, then b_1 ∪ b_2 = dN with N(g) = Re tr(F^* b_2(g)); for any action of Thompson's T by C^3 circle diffeomorphisms this kills the Hilbert-transform (Connes) Fredholm-module cocycles, the whole trace-class commutant algebra, and the Navas-Liouville cocycle as Kähler witnesses"
distinct_from:
  cup-products-of-integrably-paired-potential-cocycles-are-exact: that is the commutative case, a pairing of measurable functions on one Koopman model; this is the noncommutative dual pair (B(K), S_1(K)) under conjugation, which pairs a bounded potential with every trace-class partner even when the kernels do not pair absolutely, together with the abstract invariant-dual-pair form that contains both
  lifted-thompson-t-euler-class-in-kahler-subspace: that is the open statement (K); this removes the Fredholm-module and Liouville witness classes that the smooth Ghys-Sergiescu model of T supplies
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that kills cocycles of T-bar with a circle PVM; this is about cocycles of T and the cup-product class in H^2(T;R)
artifacts: []
---

**ESTABLISHED** by `trace-class-conjugation-cup-products-exact-proof`.

## Setting

- `G` is a group and `π` an orthogonal representation on a real Hilbert space `H`. Cup product,
  coboundary and (K) are as in `lifted-thompson-t-euler-class-in-kahler-subspace`:
  `(b_1 ∪ b_2)(g,h) = ⟨b_1(g), π(g)b_2(h)⟩`, `(dN)(g,h) = N(g) + N(h) − N(gh)`.
- *Conjugation model.* `U` is a unitary representation of `G` on a complex Hilbert space `K`.
  `S_p = S_p(K)` are the Schatten classes and `B = B(K)`. The conjugation representation
  `π_U(g)X = U_g X U_g^*` acts orthogonally on `S_2`, viewed as a real Hilbert space with
  `⟨X, Y⟩ = Re tr(X^* Y)`.
- For `F ∈ B`, put `c_F(g) = U_g F U_g^* − F`. When all its values lie in `S_2` it is a 1-cocycle
  into `π_U`. `F` is its *potential*.
- `A_1(U) = {F ∈ B : [F, U_g] ∈ S_1 for all g}`. It is a unital `*`-algebra containing `S_1`.

## Statement

**(A) Invariant dual pair.** Let `E ⊇ H` be a real vector space with a linear `G`-action `ρ`
extending `π`. Let `W ⊆ H` be a `π`-invariant subspace, and let `P : E × W → R` be bilinear,
`ρ × π`-invariant, and equal to `⟨·,·⟩` on `H × W`. If `f ∈ E`, `b_1(g) = ρ(g)f − f ∈ H` for all
`g`, and `b_2` is a 1-cocycle with values in `W`, then `b_1 ∪ b_2 = dN` with `N(g) = P(f, b_2(g))`.
Finite direct sums of such data are again such data.

**(B) Schatten pairing.** Let `2 ≤ p ≤ ∞` and `1/p + 1/p' = 1`, with `S_∞ := B`. If `F ∈ S_p`,
`c_F` is `S_2`-valued, and `b_2` is a cocycle into `π_U` with values in `S_{p'}`, then
`c_F ∪ b_2 = dN` with `N(g) = Re tr(F^* b_2(g))`. The same holds for `b_2 ∪ c_F`, and for any
`b_1, b_2` cohomologous in `Z¹(G; π_U)` to such cocycles.
- In particular, all pairwise cup products of the cocycles `c_F`, `F ∈ A_1(U) + S_2`, are exact.
- This covers complex combinations too: `c_{F_1} + i c_{F_2} = c_{F_1 + iF_2}`.

**(C) Smooth circle actions of `T`.** Let `T` act on `S¹ = R/2πZ` by orientation-preserving
`C³` diffeomorphisms. The Ghys–Sergiescu smooth model of `T` is recalled, not verified; the kill
does not need it, and is vacuous if no such action exists. Let `U` be the half-density
representation on `L²(S¹, dx)`, `(U_g φ)(x) = φ(g⁻¹x) (g⁻¹)'(x)^{1/2}`, and let `ℋ` be the
circle Hilbert transform, `(ℋφ)^(n) = −i sgn(n) φ̂(n)`. Then:
1. `c_ℋ(g) ∈ S_1` for every `g ∈ Diff³_+(S¹)`. So `ℋ ∈ A_1(U)`, and so are the Szegő
   projection and the whole `*`-algebra `A_1(U)` it generates with `S_1`.
2. Hence no pair of Fredholm-module cocycles `c_F, c_{F'}` with `F, F' ∈ A_1(U) + S_2`, and no
   pair `(c_ℋ, b)` with `b` trace-class valued, witnesses (K) unless `e_R = 0`.
3. *Navas–Liouville cocycle.* On `Ω = S¹ × S¹ ∖ Δ` with the Liouville measure
   `μ = dx dy / (4 sin²((x−y)/2))` and the diagonal action, `ν(g) = π(g)1 − 1` has values in
   `L¹(μ) ∩ L²(μ)`. So `ν ∪ b` and `b ∪ ν` are exact for every cocycle `b` of the same Koopman
   model with `L¹(μ)` values, by `cup-products-of-integrably-paired-potential-cocycles-are-exact`
   with a bounded potential.

## Named invariant and the step where every member dies

- **Invariant.** The relative trace `N(g) = Re tr(F^* b_2(g))`. It is the noncommutative
  renormalized intersection number. It is defined because a bounded potential pairs with trace-class
  values, whether or not the kernels pair absolutely.
- **Step.** `⟨c_F(g), π_U(g) b_2(h)⟩ = N(h) − Re tr(F^*(b_2(gh) − b_2(g)))`. This uses only
  the conjugation invariance `tr((U F U^*)^* U Y U^*) = tr(F^* Y)` for `F ∈ B`, `Y ∈ S_1`.
- **Why `ℋ` falls in.** The kernel of `U_g^* ℋ U_g − ℋ` is
  `(1/2π)[√(g'(x)g'(y)) cot((gx−gy)/2) − cot((x−y)/2)]`. The two singularities `2/(x−y)`
  cancel, and the kernel is `C¹` on the torus, vanishing on the diagonal. A `C¹` kernel on the
  torus is trace class.

## What survives (forced shape, sharpened)

A conjugation-model witness for (K) needs a potential `F` whose commutators `[F, U_g]` are
Hilbert–Schmidt but whose relative trace against the partner diverges. Examples are a
`2`-summable, not `1`-summable Fredholm module, or an unbounded potential outside every `S_p`,
`p < ∞`, with a partner outside `S_{p'}`. For `C³` actions on the circle, the canonical
Hilbert-transform module is `1`-summable, so it is not such a witness. Order-0 pseudodifferential
potentials with non-constant principal symbol have non-compact commutators and give no
`S_2`-cocycle at all. This last point is recalled, not proved, and not used.

## Consequence for the route

`lifted-thompson-t-a-t-menable-via-kahler-euler-class` needs (K). After this claim and
`cup-products-of-integrably-paired-potential-cocycles-are-exact`, both natural sources of unitary
cocycles for groups of smooth circle diffeomorphisms are exhausted as sources of (K). These are
Connes' Hilbert-transform Fredholm module and Navas' Liouville cocycle, the one used to exclude
property (T) for `Diff^{1+α}`. A witness must come from a representation not built from the
circle action by these two constructions.
