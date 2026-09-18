---
rg: 2
id: port-amalgams-with-a-locally-moving-factor-are-never-faithful
kind: claim
title: An amalgam or HNN extension of homeomorphism groups along a common subgroup never acts faithfully when one factor has nontrivial elements of arbitrarily small support that avoid the port; so two odometer hosts cannot be glued faithfully along the odometer under any twist, and cyclic Houghton ports never glue faithfully to anything
requires:
  - higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness
distinct_from:
  higman-closure-of-abelian-cofinite-hosts-is-port-faithfulness: that isolates faithfulness as the one clause Higman's operations fail to preserve, and shows generic gluing is unavailable; this proves faithfulness fails outright for every factor with small supports, the source of all known finitely presented hosts.
  amalgams-of-orbit-finite-actions-are-type-a2: that gives one explicit kernel element for a specific configuration; this is the general criterion, for amalgams and HNN extensions, in any Hausdorff topology.
  v-and-a-homeomorphism-never-generate-a-free-product: that is the free-product case with V; this is the amalgamated and HNN case with any locally moving factor and any continuous partner.
---

**ESTABLISHED** (lane bh-invent-02, 2026-09-18). This is a lane proof, elementary. It has not
been reviewed, and no priority is claimed.

## Statement

**Setting.**
- `K` is a Hausdorff space with at least three points, and `D_1, D_2 ≤ Homeo(K)`.
- `A ≤ D_1 ∩ D_2`, with the same action.
- `Rist(U)` is the set of elements of `D_1` that are the identity off `U`.

**Hypotheses.**
- (S) For nonempty open `U` in a neighbourhood base of every point, `Rist(U) ≠ 1` and
  `Rist(U) ∩ A = 1`.
- `D_2 ≠ A`.

1. **Amalgams.** The canonical map `D_1 *_A D_2 → Homeo(K)` is not injective. For suitable
   `d ∈ D_2 ∖ A` and nontrivial `a ∈ Rist(U)` and `b ∈ Rist(U′)`, the reduced word
   `[d a d^-1, b] = d·a·d^-1·b·d·a^-1·d^-1·b^-1` lies in the kernel.
2. **HNN extensions.** Let `t ∈ Homeo(K)` with `t A_0 t^-1 = A_1` for `A_0, A_1 ≤ D_1`, and let
   (S) hold with `A_0` and `A_1` in place of `A`. Then `⟨D_1, t | t x t^-1 = x^t (x ∈ A_0)⟩`
   does not act faithfully. The kernel contains the reduced word `[t a t^-1, b]`.
3. **Consequences.**
   - (a) *Finitary pieces.* Let `D_1 ⊇ FSym(R)` for some infinite `R ⊆ X`, and let `A` be
     torsion-free. Then `D_1 *_A D_2 ↷ X` has a kernel for **every** `D_2 ≠ A`, with no
     continuity needed. This covers the cyclic Houghton ports of
     `cofinite-abelian-subgroups-give-relative-pbh` and every group containing `FSym(X)`.
   - (b) *Two odometer hosts.* Let `B = V_(2,1)(⟨a⟩)` act on `Z ⊂ {0,1}^N`, a dense set.
     - The permutations of `Z` normalizing `⟨a⟩` are `n ↦ ±n + k`. So a second copy of `B`
       glued along `⟨a⟩` with the same action is `B` or `cBc`, where `c(n) = -1-n` is the
       digit complement. A copy glued by a Thompson element `τ` not normalizing `⟨a⟩` is an
       HNN extension with `t = τ`.
     - Every case is continuous on `{0,1}^N`, and `B` satisfies (S) because `⟨a⟩` acts freely.
     - So no twist gives a faithful gluing. For `B` and `cBc` it fails already at `V ≤ B ∩ cBc`.

## Proof

**Item 1.**
- **Choosing the sets.** Fix `d ∈ D_2 ∖ A` and a point `y`, and choose
  `x ∉ {y, d^-1(y)}`.
  - By the Hausdorff property there are disjoint open sets separating `y` from `x` and from
    `d(x)`. Let `U′ ∋ y` be small, and let `U = W ∩ d^-1(W′)`, where `W ∋ x` and `W′ ∋ d(x)`
    avoid `U′`.
  - Shrink `U` and `U′` into the neighbourhood base of (S). Then `U`, `d(U)` and `U′`
    satisfy `U ∩ U′ = ∅ = d(U) ∩ U′`.
- **Choosing the elements.** Pick nontrivial `a ∈ Rist(U)` and `b ∈ Rist(U′)`. By (S),
  neither `a^±1` nor `b^±1` lies in `A`.
- **The word acts trivially.** `d a d^-1` is supported in `d(U)`, which is disjoint from
  `U′ ⊇ supp b`, so `[d a d^-1, b] = 1` in `Homeo(K)`.
- **The word is nontrivial.** Its letters alternate between `D_2 ∖ A` (`d^±1`) and
  `D_1 ∖ A` (`a^±1`, `b^±1`). So it is reduced of length 8, hence nontrivial in the amalgam
  by the normal form theorem.

**Item 2.** Choose `U, U′` as in item 1, with `t` in place of `d`, and nontrivial `a ∈ Rist(U)`,
`b ∈ Rist(U′)`.
- `t a t^-1` is supported in `t(U)`, which misses `U′`, so the word acts trivially.
- In `t·a·t^-1·b·t·a^-1·t^-1·b^-1` a pinch needs `a^±1 ∈ A_0` or `b^±1 ∈ A_1`, and (S)
  excludes both. So the word is Britton-reduced and nontrivial.

**Item 3.**
- (a) Take 2-element sets `U, U′ ⊆ R` with `U ∩ U′ = ∅ = d(U) ∩ U′`, which is possible since
  `R` is infinite, and let `a, b` be their transpositions. They have order 2, so they are not
  in the torsion-free `A`. The item 1 argument then applies verbatim in `Sym(X)`.
- (b) A bijection conjugating the translation `a` to `a^±1` is affine. The clopen cones give
  the neighbourhood base, their rigid stabilizers contain copies of `V`, and they meet `⟨a⟩`
  trivially because `a^k` (`k ≠ 0`) moves every point. `c` is a homeomorphism normalizing `V`,
  so `V ⊆ B ∩ cBc`. ∎

## Lesson for general BH

**Small supports forbid faithful gluing.** Every finitely presented host on record is built
from locally moving pieces:
- Houghton groups, containing `FSym`;
- odometer and Thompson-type groups, which have rigid stabilizers of cones.

Every port amalgam or HNN extension of such a piece with anything continuous in the same
topology has the commutator `[d a d^-1, b]` in its kernel.

**Consequences for the host problem.** Hosts reached by Higman's operations therefore have two
options:
- use pieces with no small supports (rigid, non-locally-moving actions such as linear or
  free ones);
- remove the kernel by adding the disjoint-support commutation relations.

The second option is exactly what finite presentation theorems for Thompson-type groups do:
Brown--Stein--Farley, and the sliding lemma of `bh-invent-01`, where disjoint-support relations
follow from bounded-diameter relators.

**One gate.** Kernel removal for locally moving ports (FFWZ Question 5.9) and the
host-closure gate of the one-dimensional Higman problem are the same question. P2′ of the master
route has the same shape for full groups:

> Are the disjoint-support commutators of a locally moving glued group normally generated by
> finitely many of them?
