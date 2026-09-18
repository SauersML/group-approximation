---
rg: 2
id: circulant-graph-wreath-products-embed-in-dv-f-proof
kind: route
title: Proof that every circulant graph wreath product with cofinite connection set embeds in the finitely presented simple group DV_F, by edge-coordinate ping-pong
target: circulant-graph-wreath-products-satisfy-boone-higman
requires:
  - one-fp-simple-group-contains-every-brin-thompson-subgroup
  - twisted-brin-thompson-finite-presentation-criterion
---

Lane proof, not reviewed. The construction is this lane's own. The host is
Belk–Zaremsky's `DV_F`, which is finitely presented and simple by
`one-fp-simple-group-contains-every-brin-thompson-subgroup` item 1.

**Setting.**
- `E ⊆ N_{≥1}` is finite and `U = N_{≥1} ∖ E`.
- `G_U = A(Γ_U) ⋊ ⟨t⟩`, and `a_j = t^j a t^{-j}`. Vertices `i, j` of `Γ_U` are
  adjacent (commute) iff `|i−j| ∉ E`.
- `N_E` is the complement graph, the circulant graph with connection set `E`. It is
  locally finite, and each vertex has degree `k = 2|E|`.
- If `E = ∅`, then `G_U = Z ≀ Z ≤ F ≤ DV_F`. Assume from now on `E ≠ ∅`.

## 1. Edge coordinates

The coordinate set is the edge set of `N_E`:
- `S_E = {e_{j,d} = {j, j+d} : j ∈ Z, d ∈ E}`;
- `Z` acts on `S_E` freely by `e_{j,d} ↦ e_{j+1,d}`.

Each vertex `j` gets `k` slots `σ = (±,d)`, `d ∈ E`:
- slot `(+,d)` is `e_{j,d}`, the edge to `j+d`;
- slot `(−,d)` is `e_{j−d,d}`, the edge to `j−d`.

Write `inc(j)` for this ordered `k`-tuple of coordinates.

- **Overlaps.** `inc(i) ∩ inc(j) = ∅` unless `|i−j| ∈ E`. If `i = j+d`, the only
  common coordinate is `e_{j,d}`, which is slot `(+,d)` of `j` and slot `(−,d)` of
  `i`.

## 2. The local element

Let `C = {0,1}^N`. Choose cones `A_{(+,d)} = [01]` and `A_{(−,d)} = [10]`. They
are disjoint, and neither contains `c := 000…`.
- Choose disjoint dyadic boxes `R^+, R^- ⊆ ∏_σ A_σ ⊆ C^k`.
- Choose `h ∈ kV` with `h(C^k ∖ R^-) = R^+`, hence `h(R^-) = C^k ∖ R^+`. It
  exists because `kV` acts transitively on ordered partitions of `C^k` into two
  nonempty clopen dyadic sets.
- **North–south dynamics.** For `n ≥ 1`, `h^n(C^k∖R^-) ⊆ R^+` and
  `h^{-n}(C^k∖R^+) ⊆ R^-`.
- Put `B = R^+ ∪ R^-`, and let `Y ⊆ C^k` be the set of `y` with
  `y_{(+,d)} ∈ A_{(−,d)}` or `y_{(−,d)} ∈ A_{(+,d)}` for some `d`. Then
  `Y ∩ ∏_σ A_σ = ∅`, since `A_{(+,d)} ∩ A_{(−,d)} = ∅`. So `Y ∩ B = ∅`, and

      h^n(Y) ⊆ B   for every n ≠ 0.                                       (NS)

## 3. The action

Let `x_j` be the homeomorphism of `C^{S_E}` that applies `h` to the coordinates
`inc(j)`, in slot order, and fixes all other coordinates. Put
`X_j = {ω : ω|inc(j) ∈ B}`, and let `p` be the point with every coordinate `c`.

**(i) Relations hold.** If `|i−j| ∉ E`, then `x_i` and `x_j` act on disjoint
coordinate sets, so they commute, and `x_i(X_j) = X_j`.

**(ii) Ping-pong for non-adjacent pairs.** Let `i = j+d`, `d ∈ E`.
- **The shared coordinate.** If `ω ∈ X_i`, then its value at the shared coordinate
  `e_{j,d}` lies in `π_{(−,d)}(B) ⊆ A_{(−,d)}`.
- **In `j`'s slots.** That coordinate is slot `(+,d)` for `j`, so
  `ω|inc(j) ∈ Y`.
- **Conclusion.** By (NS), `x_j^n(ω)|inc(j) = h^n(ω|inc(j)) ∈ B`, that is,
  `x_j^n(X_i) ⊆ X_j` for `n ≠ 0`.
- **The case `i = j−d`** is symmetric: slot `(+,d)` of `i` is slot `(−,d)` of `j`.

**(iii) Basepoint.** `p|inc(j) = (c,…,c) ∉ ∏_σ A_σ`. So `p ∉ X_j`, and by (NS)
`x_j^n(p) ∈ X_j` for `n ≠ 0`.

**(iv) Faithfulness.** Ping-pong for right-angled Artin groups, proved here for
arbitrary graphs.
- **The statement.** Suppose a group acts on a set with elements `g_v`, subsets
  `X_v`, and a point `p ∉ ∪X_v` such that:
  - `g_v^n(X_u) ⊆ X_v` for `u ≠ v` non-adjacent and `n ≠ 0`;
  - `g_v(X_u) = X_u` for `u, v` adjacent;
  - `g_v^n(p) ∈ X_v` for `n ≠ 0`.

  Then `v ↦ g_v` is injective on `A(Γ)`.
- **The claim.** Every nontrivial `w` satisfies `w(p) ∈ X_u` for some first letter
  `u` of `w`. Induct on the length of a minimal-length word.
  - **Splitting.** Write `w = s^n w'` with `n ≠ 0` and `s` not a first letter of
    `w'`. Pull every front-shufflable `s`-syllable forward; by minimality they do
    not all cancel.
  - **Base case.** If `w' = 1`, use the third condition.
  - **Inductive step.** Otherwise `w'(p) ∈ X_u` for some first letter `u ≠ s` of
    `w'`.
    - If `u` and `s` are non-adjacent, then `w(p) ∈ s^n(X_u) ⊆ X_s`, and `s` is a
      first letter of `w`.
    - If they are adjacent, then `w(p) ∈ X_u`, and `u` shuffles past `s^n`, so it
      is a first letter of `w`.
- **Conclusion.** Since `p ∉ ∪X_v`, we get `w(p) ≠ p`. By (i)–(iii), `a_j ↦ x_j`
  is a faithful action of `A(Γ_U)`. A word involves only finitely many vertices,
  so the infinite graph causes no difficulty.

## 4. The shift and the host

- **The coordinate set.** `F` acts on the dyadic rationals `D ⊂ (0,1)`. Its
  generator `x_0` satisfies `x_0(s) > s` on `(0,1)`, so every orbit in `D` is
  bi-infinite.
- **Placing the coordinates.** Choose distinct dyadics `s_d ∈ [1/4,1/2)`, one for
  each `d ∈ E`. They lie in one fundamental domain, so they have distinct orbits.
  Identify `e_{j,d}` with `x_0^j(s_d)`. This embeds `S_E ⊆ D`, and `t` acts as
  `x_0`.
- **Elements of `DV_F`.** In `DV_F`, `x_0` acts on `C^D` by permuting coordinates.
  Each `x_j` is an untwisted Brin–Thompson element supported on the finitely many
  coordinates `inc(j) ⊆ D`, so both lie in `DV_F`. Moreover
  `x_0 x_j x_0^{-1} = x_{j+1}`, because conjugation transports supports and slot
  order.
- **The map.** So `a ↦ x_0` (the vertex element at `j = 0`), `t ↦ x_0 ∈ F`
  defines a homomorphism `φ : G_U → DV_F`, which is injective on `A(Γ_U)`.
- **Injectivity.** Let `K = ker φ`. Then `K ∩ A(Γ_U) = 1`, and both are normal, so
  `[K, A(Γ_U)] = 1`.
  - An element `α t^m ∈ K` with `m ≠ 0` would conjugate each `a_j` to `a_{j+m}`
    inside `A(Γ_U)`.
  - That contradicts `A(Γ_U)^{ab} = ⊕_j Z e_j`, where `e_j ≠ e_{j+m}`.
  - So `K = 1`, and `G_U ≤ DV_F`.

The construction is uniform in `E`, and one host `DV_F` serves every `E`.

## 5. General form

The argument used only that the non-commutation graph `N = Γ^c` is locally
finite.
- **The lemma.** For every countable graph `Γ` whose complement is locally finite,
  `A(Γ)` embeds in the finitary Brin–Thompson group on `C^{edges(N)} ⊆ C^D`, and
  hence in `DV_F`.
- **The construction.**
  - Orient each edge, and give its two endpoints the disjoint cones `[01]` and
    `[10]` at that coordinate.
  - Take `h_v` north–south in `deg(v)V`.
  - An isolated vertex of `N` gets one private coordinate.
- **Equivariance.** It holds whenever a group acts freely on the vertices, as
  `Z` does here.
