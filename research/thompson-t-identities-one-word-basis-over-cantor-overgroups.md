---
rg: 2
id: thompson-t-identities-one-word-basis-over-cantor-overgroups
kind: claim
title: One three-arc mixed identity E of Thompson's T forces all of them in every overgroup of homeomorphisms of the Cantor set or the circle, because a group satisfying E must preserve the cyclic order
requires:
  - thompson-t-identities-one-word-basis-proof
distinct_from:
  circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities: that proves groups of orientation-preserving circle homeomorphisms containing T satisfy every mixed identity of T; this proves that inside all homeomorphisms of the Cantor set or the circle, one identity E already forces orientation preservation, so E is a basis there.
  fp-simple-group-with-non-finitely-based-mixed-identities: that asks for a finitely presented simple group whose mixed identities have no finite basis over overgroups; this rules out Thompson's T as a witness through any overgroup acting on the Cantor set or the circle extending T's standard action.
  thompson-t-mixed-identities-are-not-finitely-normally-generated: that answers BFFHZ Question 3.3 negatively, using V-elements supported in small clopen sets, which are not substitution-closed; this is about finite bases closed under substitution, where the same V-overgroup is caught by the single word E.
  bffhz-q32-for-fp-simple-groups: that is BFFHZ Question 3.2, still open for T; this removes every dynamical overgroup as a source of the obstruction that bffhz-q32-forces-finitely-based-mixed-identities would need.
---

**ESTABLISHED** by `thompson-t-identities-one-word-basis-proof`. Lane proof by bh-ffwz-q59,
2026-09-18. It is elementary and not reviewed. No priority is claimed: the three-arc mechanism is
Le Boudec--Matte Bon's, and the word is a variant of (CA1) in
`homeo-circle-three-arc-commutator-word-is-mixed-identity`.

## Setting

- **The spaces.** `C = {0,1}^N` carries its lexicographic cyclic order. `T ≤ V ≤ Homeo(C)` acts
  through binary expansions: `T` is the subgroup of `V` preserving the cyclic order.
  `Homeo_cyc(C)` is the group of homeomorphisms of `C` preserving the cyclic order.
- **Mixed identities.** For `T ≤ M` put `J_k(M; T) = {w ∈ T * F_k : w(g) = 1 for all g ∈ M^k}`,
  and write `J_k(T) = J_k(T; T)`.

## Statement

There is one word `E ∈ J_1(T)`, written out in the proof, with the following property. Let
`X ∈ {C, S^1}`, and let `M ≤ Homeo(X)` contain `T` in its standard action, or in a conjugate of
it. If `E(g) = 1` for every `g ∈ M`, then:
1. `M` preserves the cyclic order: `M ≤ Homeo_cyc(C)`, respectively `M ≤ Homeo_+(S^1)`;
2. `J_k(M; T) = J_k(T)` for every `k ≥ 1`.

So `{E}` is a finite basis for all mixed identities of `T`, relative to overgroups that act on the
Cantor set or the circle and extend the standard action of `T`.

## Consequences

- **No dynamical witness.** A witness overgroup `M_W` for
  `fp-simple-group-with-non-finitely-based-mixed-identities` at `S = T` would satisfy a finite
  `W` but not all of `J_1(T)`. Putting `E` into `W` shows that no such `M_W` acts on `C` or on
  `S^1` extending the standard `T`.
  - This covers `V`, every Röver--Nekrashevych-type Cantor group containing `T`, every group
    obtained from `T` by adding one order-breaking homeomorphism, and all circle groups.
  - Circle groups were already handled by `circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities`.
- **Where a NO for BFFHZ Question 3.2 at `T` could come from.** Via
  `bffhz-q32-forces-finitely-based-mixed-identities`, it would have to use an abstract overgroup
  of `T` that admits no faithful action on `C` extending `T`'s.
- **What is not claimed.**
  - A finite basis over all abstract overgroups.
  - Overgroups in which `T` acts non-standardly, such as the Denjoy blow-ups along rational orbits
    that survive Attempt 5 of `fp-simple-group-with-non-finitely-based-mixed-identities`. There `T`
    cannot move arcs into gaps, and Step 2 of the proof fails.
  - Any answer to Question 3.2 for `T`: the finite-basis condition is only necessary.

## Lesson for general BH

For circle-type hosts, the mixed identities have a single cause, which is orientation. One
identity detects any break of orientation, anywhere and at any scale.
- **Why one identity suffices.** A host that is transitive and contracting in the manner of `T`
  can move a local break to any position. It can then squeeze three independent conjugates
  into one arc, where a nested commutator sees them.
- **So kernel removal for circle-type Theorem C actors is not blocked by dynamics.** Any
  obstruction to BFFHZ Question 3.2 for `T` must be purely algebraic: an abstract `T`-group
  that satisfies `E` and cannot act on a circle or a Cantor set extending `T`.
- **The dynamical evidence points to a yes for Question 3.2 at `T`.** A proof would still
  have to go from this finite basis to finite normal generation of the actor kernel.
