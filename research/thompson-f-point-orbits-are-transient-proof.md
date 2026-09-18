---
rg: 2
id: thompson-f-point-orbits-are-transient-proof
kind: route
title: Plant a transient component of the deep dyadic Schreier graph in every tail class by appending a non-periodic tail, then use quotients and heredity
target: thompson-f-point-orbits-are-transient
requires:
  - f-dyadic-action-is-not-recurrent
  - lyons-peres-energy-rough-embedding-and-polya-transience
  - recurrent-orbits-force-every-z3-to-meet-the-stabilizer
---

**Model.** Let `π : {0,1}^N → [0,1]`, `π(x) = Σ x_i 2^(-i)`. For a finite word `w`, the
cylinder `[w]` is an interval of length `2^(-|w|)`, and `x ↦ wx` is affine onto it with slope
`2^(-|w|)`. On `{0,1}^N` define
- `x_0 : 00s ↦ 0s, 01s ↦ 10s, 1s ↦ 11s`;
- `x_1 : 0s ↦ 0s, 1s ↦ 1·x_0(s)`.

Under `π` these are PL maps with dyadic breakpoints and slopes in `2^Z`:
- `x_0` is `t ↦ 2t` on `[0,1/4]`, `t ↦ t + 1/4` on `[1/4,1/2]`, and `t ↦ t/2 + 1/2` on `[1/2,1]`;
- `x_1` is the identity on `[0,1/2]` and `x_0` conjugated into `[1/2,1]`.

They are the inverses of the standard generators, so they generate `F`. The map `π` is
`F`-equivariant. It is injective off the words ending in `0^∞` or `1^∞`, and on each dyadic
point it identifies `u10^∞` with `u01^∞`.

Let `S = {x_0^(±1), x_1^(±1)}`. Each rule rewrites a prefix of length at most 3 into a
prefix whose length differs by at most 1. Hence:

**(R) Rewriting.** If `|u| ≥ 4` and `σ ∈ S`, there is a word `σ̂(u)` with `σ(uy) = σ̂(u)y`
for every infinite word `y`. It has the form `σ̂(u) = r·u_(k+1)…u_(|u|)` with `k ≤ 3`
and `|r| ≥ k − 1`. In particular `|σ̂(u)| ≥ |u| − 1`, and `σ̂(u)` ends with the same letter
as `u`.

**(P) Prefix replacement.** Let `v, u` be finite words that each contain both letters. Then
there is `g ∈ F` with `g(vx) = ux` for all infinite words `x`.

*Proof of (P).* The complement of `[v]` in `{0,1}^N` is covered by two ordered families of
cylinders:
- on the left, `v_1…v_(i−1)0` for each `i` with `v_i = 1`;
- on the right, `v_1…v_(i−1)1` for each `i` with `v_i = 0`.

Both families are nonempty. Replacing a cylinder `w` by `w0, w1` adds one cylinder to a
family, so we may pad the families of `v` and of `u` to equal sizes on each side. This gives
complete prefix codes `P ∋ v` and `Q ∋ u` of equal size, with `v` and `u` in the same
position. The order-preserving bijection `P → Q`, applied as `px ↦ qx`, is a homeomorphism
of `[0,1]`: the cylinders of a complete prefix code tile `[0,1]` in order. It is affine on
each cylinder with slope in `2^Z` and dyadic breakpoints, so it lies in `F`, and it maps
`vx` to `ux`. ∎

**Step 1 (the dyadic graph as words).** Let `W` be the set of finite words ending in `1`.
The map `u ↦ π(u0^∞)` is a bijection from `W` onto `D = Z[1/2] ∩ (0,1)`, and it is
`F`-equivariant for the induced action on `W`. So `Sch(D, S)`, which is transient by
`f-dyadic-action-is-not-recurrent`, is the network on `W` in which the conductance between
`u ≠ u′` is `#{σ ∈ S : σ(u0^∞) = u′0^∞}`.

Let `B = {u ∈ W : |u| < K}` with `K ≥ 4`. This set is finite and contains `o = 1`.

*A transient component of `W ∖ B` (induced network).* By Lyons–Peres Theorem 2.11 there
is a unit flow `θ` from `o` to `∞` with finite energy. Let `C_1, …, C_r` be the components of
`W ∖ B`:
- each contains a neighbour of `B`, because `Sch(D,S)` is connected;
- there are finitely many, because `B` is finite and degrees are at most 4.

Restrict `θ` to the edges inside `C_j`. Its divergence is supported on the finitely many
neighbours of `B` in `C_j`, with total `m_j` equal to the net flow of `θ` from `B` into
`C_j`. Since `div θ = δ_o` and `o ∈ B`, we have `Σ_j m_j = Σ_(x ∈ B) div θ(x) = 1`, so some
`m_j > 0`.

In the connected network `C_j`, add finite path flows from one vertex `o′` to each point of
that divergence. This changes the energy by a finite amount, and the divergence becomes
`m_j δ_(o′)`. Dividing by `m_j` gives a finite-energy unit flow from `o′` to `∞`, so `C_j` is
transient by Theorem 2.11. Put `T := C_j`.

**Step 2 (planting `T` into a tail class).** Let `s` be an infinite word that is not purely
periodic, i.e. `s ≠ y^∞` for every finite word `y`. Define `φ_s(u) = us` for `u ∈ T`.

- *Edges.* If `u, u′ ∈ T` and `σ(u0^∞) = u′0^∞`, then by (R) `σ̂(u) = u′`, because
  `σ̂(u)` ends in `1`. Hence `σ(us) = u′s`. So every labelled edge of `T` maps to a
  labelled edge between the images, and conductances do not decrease.
- *Injectivity.* Suppose `us = u′s` with `|u| ≤ |u′|`. If the lengths are equal, `u = u′`.
  Otherwise `u′ = uw` with `w` nonempty, and `s = ws`, so `s = w^∞`, contrary to the choice
  of `s`.
- *Rough embedding.* `φ_s` is injective on vertices and sends each edge to one edge. So it is
  a rough embedding of `T` into the Schreier network of the `F`-orbit of `u_0 s`
  (`u_0 ∈ T`) on `{0,1}^N`, with `α = β = 1`. By Lyons–Peres Theorem 2.17 that orbit is
  transient.
- *To the interval.* If `s` is not eventually constant, `π` is injective and equivariant on
  the orbit. Then `F·π(u_0 s)` has the same Schreier network and is transient.

**Step 3 (every point of `(0,1)`, item 1).** Let `t ∈ (0,1)`.

- **Dyadic `t`.** `F·t = D` is transient by the import.
- **Otherwise.** The expansion `e(t)` is not eventually constant. Choose `s` and a prefix
  decomposition as follows, and fix any `u_0 ∈ T`.
  - *`e(t)` not eventually periodic.* Put `s = e(t)`. It is not purely periodic. Write
    `s = yx` with `y` a prefix containing both letters. Then `u_0 s = (u_0 y)x` and
    `e(t) = yx`.
  - *`e(t) = v w^∞`* with `w` primitive of length `P ≥ 2`. `w` contains both letters, since
    `e(t)` is not eventually constant. Put `s = 0^P w^∞`. Then `u_0 s = (u_0 0^P w) w^∞` and
    `e(t) = (vw) w^∞`.
    - *`s` is not purely periodic.* If `s = y^∞`, every finite factor of `s` occurs
      infinitely often in `s`, hence in its tail `w^∞`. But `0^P` is a factor of `s`, while
      every window of length `P` in `w^∞` is a rotation of `w` and contains a `1`.

  In both cases the two prefixes contain both letters. By (P) some `g ∈ F` maps `e(t)` to
  `u_0 s`, so `F·t = F·π(u_0 s)`, which is transient by Step 2.
- **Generating sets.** By item 1 of `recurrent-orbits-force-every-z3-to-meet-the-stabilizer`,
  transience does not depend on the generating set.

**Cantor set.** Let `x ∈ {0,1}^N ∖ {0^∞, 1^∞}`.
- If `x` is not eventually constant, `π` identifies `F·x` with `F·π(x)`.
- If `x` is eventually constant, `x = u10^∞` or `x = u01^∞`. Then `π` maps `F·x` equivariantly
  onto `D`.

In both cases `F·x` maps equivariantly onto a transient orbit, so it is transient by (Q)
below.

**(Q) Recurrence passes to quotients.** Let a group with finite symmetric generating
multiset `S` act on two sets, and let `q : G·y → G·x` be an equivariant surjection. Let
`Y_n = s_n ⋯ s_1 y` with the `s_i` i.i.d. uniform in `S`. Then `q(Y_n) = s_n ⋯ s_1 x` is the
same walk on `G·x`. Deleting loop steps only delays these walks, so they have the same type as
the network walks. If `Y_n = y` infinitely often almost surely, then `q(Y_n) = x` infinitely
often. So a transient quotient has a transient cover.

**Item 2.** If `Stab_F(y) ⊆ Stab_F(t)` with `t ∈ (0,1)`, then `g y ↦ g t` is a well-defined
equivariant surjection `F·y → F·t`. Items 1 and (Q) give transience.

**Item 3.** Let `K = θ(ι_p(F))`, generated by `θι_p(S)`, and `y′ ∈ G·y`.
- By heredity (item 1 of `recurrent-orbits-force-every-z3-to-meet-the-stabilizer`),
  `K·y′` is recurrent.
- Suppose `ι_p^(-1)θ^(-1)(G_(y′))` fixes `t ∈ (0,1)`. Then `θι_p(g) y′ ↦ g t` is well defined.
  Transported through the isomorphism `θι_p : F → K`, it is an equivariant surjection from
  `K·y′` with generators `θι_p(S)` onto `F·t` with generators `S`.
- The walks correspond as in (Q), so `F·t` is recurrent, contradicting item 1.

The equivalent form holds because `ι_p` conjugates the action on `(0,1)` to the action on
`int [p]`. For `G = F`, `θ = id` and `p` empty: `Stab_F(y′)` fixes no point of `(0,1)`. A
subgroup of `F` with no fixed point in `(0,1)` has `(0,1)` as its only orbital. ∎
