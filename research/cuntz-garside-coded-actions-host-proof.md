---
rg: 2
id: cuntz-garside-coded-actions-host-proof
kind: route
title: The Cuntz F_infinity proof runs with finite unit groups once types are counted up to units (Dickson on unit classes, unit-twisted loops for the height, finite cell stabilizers); comparison, Li's Corollary D, Matui's theorem and a prefix-code wreath give the simple host and finite-index closure
target: cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups
requires:
  - cuntz-stabilized-garside-full-groups-are-f-infinity
  - cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
---

**Lane proof, not independently reviewed.** Notation is that of the target and of
`cuntz-stabilized-garside-full-groups-f-infinity-proof` (below, "the Cuntz proof"). Labels are
Li's (arXiv:2110.04505v2).

## 1. Item 1 with finite unit groups

The Cuntz proof assumed `𝔠* = 𝔠⁰`. Units are used at five places. With finite unit groups,
each goes through as follows. Write `u·X(v;e) = X(t(u); u e)` for units `u`. Two types are
**unit-equivalent** if a unit carries one onto the other, and `𝒯` denotes the finite set of
unit classes of types occurring in `𝐗(*)`.

**(U1) The pure-hole datum.** `𝔠₂* = 𝔠* × {1}`, and a unit carries pure holes to pure holes.
- **(`1_𝔛`)** holds.
- **(`3_Γ`).** For `α = (a_i X(𝐝a_i; f_i))_i ∈ 𝚪` and a unit `u`, write `u a_i = a'_i u'_i`
  with `a'_i` in the chosen `=*`-transversal of `𝔖₂`. Then
  `uα = (a'_i X(𝐝a'_i; u'_i f_i))_i · ([u'_i, X(𝐝a_i;f_i)])_i`.
  - The first factor is one-layer, because units preserve norms.
  - Its pieces are pure, so it lies in `𝚪`.
- **(`4_Γ`), (`5_Γ`).** The proofs in `cuntz-pure-hole-datum-satisfies-li-st-and-lcm` hold
  verbatim, since they only use mcms up to `=*`, right-divisor closure of `𝔖₂^♯`, and purity.
- **Li's hypotheses on `𝔠₂`.** Right cancellation (hence (F)), disjoint mcms and the Garside
  family pass to `𝔠 × M` componentwise.

**(U2) Objects up to units.** Let `x = (U_i)` and `y = (V_j)` have the same multiset `𝐦̄` over
`𝒯`.
- Choose a bijection `π : I → J` and units with `V_{π(i)} = u_i·U_i`. Then `([u_i,U_i])_i`
  is a unit of `𝐂_𝐗`, because both types lie in `𝔛` by (`1_𝔛`).
- `𝐗(*)` is closed under composition with units of `Π`.
- So `x ∈ 𝐗(*)` iff `y ∈ 𝐗(*)`, and unit-classes of objects are the multisets `𝐦̄`.

**(U3) Lemma L.** Run the proof of Lemma L in the Cuntz proof (§5) with `𝐦̄` in place of `𝐦`.
- **Doubling.** `𝐦̄ + e_{[τ]} ∈ 𝐑` whenever `𝐦̄([τ]) ≥ 1`, via `δ_τ` (§E of
  `cuntz-pure-hole-datum-satisfies-li-st-and-lcm`).
- **Dickson.** Each support class of `𝐑` has finitely many minimal elements. This gives the
  constant `C` and eventual downward closure.
- **The extension.** Take `C+2` untouched pieces of a class `[τ]`. They may have different
  types `τ` and `u·τ`. The merge of a `τ`-piece and a `u·τ`-piece is
  `α = δ_τ ∘ (id ⊔ [u^{-1}, u·τ])`. It is an atom of `𝒮` up to a unit on the domain side, and
  Li's `E(x)` is taken modulo units anyway.
- **Conclusion.** Applying `α` to `O_l` gives the multiset `𝐦̄_{O_l} − e_{[τ]} ∈ 𝐑`. By
  (U2) this is an object of `𝐗(*)`.

**(U4) The height.** Build the one-piece relation of §4 of the Cuntz proof on `𝒯`: an edge
`[U] → [U']` whenever `U = s·V` with `s ∈ 𝔖^♯` a non-unit and `[V] = [U']`.
- **No cycles.** A cycle gives `U_0 = s_0 u_1 s_1 u_2 ⋯ s_{p−1} u_p · U_0`, with units `u_i`.
  The product `σ = s_0 u_1 ⋯ u_p ∈ 𝔠(v,v)` is a non-unit: if `ab` is a unit, then `a` has a
  right inverse, and by left cancellation `a` is a unit.
  - So `U_0 ⊆ ∩_m σ^m X(v)` is a nonempty open set, contradicting (C3).
- **The height.** `ρ_h` is defined on unit classes, as in §4 of the Cuntz proof. It is
  unit-invariant, a height, and has finite sublevels by (U2).

**(U5) Cell stabilizers.** Li's `lem:Stab` gives `𝒞*(x,x)` as an extension of a subgroup of
`Perm(I)` by `∏ 𝒞*(U_i,U_i)`, with each `𝒞*(U_i,U_i) ≤ 𝔠*(v_i,v_i)` finite. So `𝒞*(x,x)`
is finite, hence of type `F_∞`.

**Conclusion.** With (U1)–(U5), §5 of the Cuntz proof applies unchanged:
- `lem:link:n-conn_1` as stated;
- Lemma L for `lem:link:n-conn_3`;
- Li's deduction of `_2`;
- `cor:link:n-conn` with `ρ_h`;
- Witzel's `thm:Wit`.

So `S` is of type `F_∞`.

## 2. Item 2: simplicity

- **Pure infiniteness.** `(𝒢 × G_2)|_{Y×C}` is ample, with Cantor unit space (`Y` has no
  isolated points). It is Hausdorff and effective, since `𝒢|_Y` is by (C4) and `G_2` is.
- **Minimality and comparison.** It is minimal (products of minimal groupoids). It has
  comparison by Li's pure-infiniteness criterion.
  - Given clopen `U` and `V ⊇ B × C_w`, minimality and compactness split `U` into pieces
    `U_j`, each carried into `B` by a compact open bisection of `𝒢`.
  - Send the pieces into disjoint subcones `C_{w u_j}`, exactly as in Step 3 of
    `cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple`.
- **Homology.** `H_*((𝒢×G_2)|_{Y×C}) = 0`, by Matui's Künneth formula and `H_*(G_2) = 0`.
- **Li's Corollary D** (quoted verbatim on main) makes `S` integrally acyclic and `S = D(S)`.
- **Matui's `simple2`** makes `D(S)` simple. Proper infiniteness of every clopen set is
  witnessed by the two Cuntz maps.

So `S` is simple.

## 3. Item 3: the embedding

- By (C2), each `g ∈ G` is a global bisection `β_g` of `𝒢|_Y`.
- By effectiveness (C4), `β_g` is determined by its homeomorphism. So `g ↦ β_g` is an
  injective homomorphism.
- `β_g × C` is a global bisection of the product. So `g ↦ β_g × id` embeds `G` in `S`.

## 4. Item 4: finite-index overgroups

**`S ≀ Q ≤ S`.** Choose a prefix code `{w_q : q ∈ Q}` in `{x,y}^*` that covers `C`.
- The reduction of `𝒢 × G_2` to `Y × C_{w_q}` is isomorphic to the reduction to `Y × C`, via
  `(y, w_q z) ↦ (y,z)`.
- So `S_q := F(reduction to Y × C_{w_q})`, extended by the identity, is a copy of `S`. The
  copies commute and generate `∏_q S_q`.
- `Q` permutes the cones through the global bisection `(y, w_q z) ↦ (y, w_{πq} z)`, which is
  in `S`. This gives `S ≀ Q ≤ S`.

**Overgroups.** Let `H ≤ K` with `[K:H] < ∞` and `H ↪ S`.
- The normal core `N ⊴ K` has finite index and embeds in `S`.
- By Krasner–Kaloujnine, `K ↪ N ≀ (K/N) ≤ S ≀ (K/N) ≤ S`. ∎

## Lesson for general BH

Finite cell stabilizers change nothing in Li-type finiteness once types are counted **up to
units**. Dickson's lemma, the doubling atom and the height all live on unit classes. So hosts
may carry torsion in their codings for free, and torsion in the input is never an obstruction
for this route. The only unit-sensitive point is effectiveness. That is a dynamical property
(topological freeness), not a combinatorial one.
