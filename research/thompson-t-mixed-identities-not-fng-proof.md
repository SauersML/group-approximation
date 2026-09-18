---
rg: 2
id: thompson-t-mixed-identities-not-fng-proof
kind: route
title: Mixed identities of T hold for all maps with small generic support, V breaks one at every scale, so no finite set normally generates them
target: thompson-t-mixed-identities-are-not-finitely-normally-generated
requires:
  - homeo-circle-three-arc-commutator-word-is-mixed-identity
  - bffhz-q33-is-normal-finite-generation-of-mixed-identities
---

Lane proof. The only external facts used are standard:
- `T ≤ V` acting on `C` (each element of `T` lifts to a prefix-replacement map);
- PL maps have finitely many breakpoints;
- `T` has infinite-order elements supported in any dyadic arc, e.g. a copy of `F`.

**Setup.** Write `w ∈ T * ⟨x⟩` as a word of letters, each a constant `g ∈ T` or `x^{±1}`.
- For any bijection `y` of `C` read `w(y)` right to left.
- Let `Π` be the finite set of all products of consecutive constant letters, with
  the `x`-letters between them skipped. That is, for positions `i < j`, take the
  product of the constants strictly between `i` and `j`.
- Each `π ∈ Π` acts on `C` through its lift.
- Let `E ⊆ C` be the set of points fixed by some `π ∈ Π` at which that `π` is not
  the identity on any neighbourhood.
- On the circle a PL map fixes a finite union of points and closed arcs. So the
  exceptional circle points are finitely many, and `E` (their preimages) is finite.

## Part 1

Let `w ∈ J_1(T)` and `u ∉ E`. Choose a cone `U ∋ u` so small that every `π ∈ Π`
either satisfies `π(U) ∩ U = ∅` (if `π(u) ≠ u`) or is the identity on `U` (if `π`
is the identity near `u`). This uses continuity and finiteness of `Π`.

Let `P` be any homeomorphism of `C` supported in `U`, so `P(U) = U`. Follow the
trajectory of a point `z` under `w(P)`. Call an `x`-letter *active* if the current
point lies in `U` when that letter is applied. Inactive `x`-letters act trivially.
- **No active letter.** Then `w(P)(z) = w(1)(z) = z`, because `w(1)` is the product
  of the constants and equals `1` (as `w ∈ J_1`).
- **Otherwise.** Let `j` be the first active position, the entry position.
  - Between two consecutive active letters, the point starts in `U` and ends in
    `U`. The constant product `π ∈ Π` between them therefore meets `U` inside `U`,
    so `π` is the identity on `U`.
  - For the same reason, which later letters are active is fixed by `Π`. It is the
    same for every point of `U` and every `P` supported in `U`.
  - So `w(P)(z) = π_1 P^{s(j)} π_0 (z)`. Here `π_0` is the constant product to the
    right of `j`, with `π_0(z) ∈ U`. `π_1` is the constant product to the left of
    the last active letter. `s(j)` is the signed count of active letters, and it
    depends only on `j`. As above, `π_1 π_0 (z) = w(1)(z) = z`.
- **Entry is uniform.** Take `y ∈ U` at an `x`-position `j`, and an earlier
  `x`-position `k` (to the right). The point at `k` is `π''^{-1}(y)`, where `π''`
  is the constant product between `k` and `j`. It lies in `U` iff `π''` is the
  identity on `U`. So either every `y ∈ U` enters at `j`, or none does. For an
  entry position `j`, the points `π_0(z)` with `z` entering at `j` make up all of
  `U`.
- **Conclusion.** Fix an infinite-order `t ∈ T` whose lift is supported in `U`.
  Everything above applies to `t` as well. From `w(t) = 1` we get that `t^{s(j)}`
  fixes every point of `U`. So `t^{s(j)} = 1`, and `s(j) = 0` for every entry
  position. Hence `w(P)(z) = π_1 π_0 (z) = z` for every `z`, i.e. `w(P) = 1`.

## Part 2

Given a nonempty clopen `U`, choose a dyadic arc whose preimage lies in `U`. Inside
it choose three disjoint dyadic arcs `A_1, A_2, A_3` in cyclic order, and nontrivial
`a_i ∈ T` supported in `A_i`. By `homeo-circle-three-arc-commutator-word-is-mixed-identity`,
`w_U = [[s_12, s_21], s_33]` is a mixed identity of `T`. Step 5 there gives its
reduced form: `w_U = g_0 x^{e_1} g_1 ⋯ x^{e_m} g_m`, where every interior constant `g_i`
is a nontrivial product of the `a_k^{±1}` and so is supported in `U`.

Fix a tail class `Q` of `C`. Lifts of `T` and elements of `V` preserve tail
equivalence.

*Extension lemma.* Every finite partial injection `f` of `Q ∩ U` extends to some
`P ∈ V` supported in `U`.
- Write each `p_i = α_i r_i` and `f(p_i) = β_i r_i` with a common tail `r_i`.
- Lengthen the `α_i` and `β_i` by the same letters of `r_i` until the cones
  `[α_i]` are pairwise disjoint, the cones `[β_i]` are pairwise disjoint, and all
  of them lie inside `U` without covering it.
- Map `α_i s ↦ β_i s`. Match the two complements in `U`: both are nonempty clopen,
  hence finite unions of cones, and splitting cones equalizes their numbers.
- Take `P` to be the identity off `U`.

*Generic trajectory.* Build the trajectory of a point `p ∈ Q ∩ U` under `w_U`,
reading right to left, and define `x` step by step as a partial injection.
- Each application of `x^{±1}` sends the current point to a fresh point of `Q ∩ U`.
- When the next letter is an interior constant `g_i`, the fresh point is chosen in
  the open set `supp(g_i) ∩ U`, where `g_i` moves it.
- Every choice avoids all points used so far, and so does its image under the
  next constant. Each set of candidates is infinite, so this is possible.
- Because every point is fresh, the rule defining `x` stays a well-defined finite
  partial injection.
- Choose the last fresh point `r` so that `g_0(r) ≠ p`.

Extend `x` to `P ∈ V` supported in `U` by the lemma. Then `w_U(P)(p) = g_0(r) ≠ p`,
so `w_U(P) ≠ 1`.

## Part 3

This is as in the claim: parts 1 and 2 give `w_U ∉ ⟨⟨W⟩⟩` for every finite
`W ⊆ J_1(T)`. Descent (`bffhz-q33-is-normal-finite-generation-of-mixed-identities`,
part 2) handles every `n >= 1`. ∎
