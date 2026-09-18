---
rg: 2
id: quantum-rigid-minimal-topfree-subshift-actions-are-amenable
kind: claim
title: Every minimal, topologically free, quantum-rigid subshift action of a finitely generated group is topologically amenable (open); if so, the master route's object (★′) exists over no non-exact group and cannot reach Osajda's decidable non-exact group
requires:
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - decidable-residually-finite-non-exact-group-exists
refuted_by:
  - rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer
distinct_from:
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that shows Boone–Higman forces a finitely presented simple non-exact group; this asks whether the master route's rigid dynamics can ever be non-amenable, which that group would need if it came from this route.
  amenable-groupoid-full-groups-are-exact: that asks whether full groups of amenable groupoids are exact; this asks whether quantum rigidity forces the transformation groupoid to be amenable in the first place.
  master-route-needs-only-topological-freeness: that reduces the route to (★′); this is the analytic obstruction to (★′) that no current tool rules out.
---

**OPEN.** Posed by lane bh-star-b, 2026-09-18, as the adversarial form of (★′). No claim is made
either way; the evidence is below.

## Statement

Let `Λ` be finitely generated and `X ⊆ A^Λ` a nonempty subshift on which `Λ` acts minimally and
topologically freely. If `X` is `D`-quantum rigid over some field for some `D`, then `Λ ↷ X` is
topologically amenable.

## Why it decides something

Two standard facts are recalled here, not re-read:
- (F1) a countable group is exact iff it has a topologically amenable action on a compact space;
- (F2) exactness passes to subgroups.

**If the statement holds.**
- Let `G` be the decidable non-exact group of `decidable-residually-finite-non-exact-group-exists`.
  Every `Λ_0 ⊇ G` is non-exact by (F2), so by (F1) it has no topologically amenable action.
- Hence (★′) (`master-route-needs-only-topological-freeness`) has no solution over any `Λ_0 ⊇ G`.
- The conditional theorem BH ⇐ (★′) ∧ (K′) ∧ Khanh then says nothing about `G`, and neither does
  the group route, which also needs (★′).
- So the master route would be confined to exact inputs. Boone–Higman itself would not be touched.
- A second consequence: over a non-amenable `Λ`, no such `X` carries an invariant probability
  measure, since an amenable action with an invariant probability measure forces `Λ` to be amenable
  (standard, recalled).

**If the statement fails.** The counterexample would be the first quantum-rigid, minimal,
topologically free subshift whose action is not amenable. This is exactly the kind of dynamics a
finitely presented simple non-exact group would need, if it came from this route.

## Evidence (calibrated)

1. **Every proved rigid example is amenable.**

   | Example | Why the action is amenable |
   |---|---|
   | Ledrappier and permutive triangles over `Z^2` | the group is amenable |
   | end shift over `F_n`; `∂T_m ⊠ ∂T_n` | boundary actions of hyperbolic groups are amenable (Adams, recalled), and so are their products for product groups |
   | Ã₂ boundary skew shifts | boundary actions of Euclidean-building lattices are amenable (recalled, not re-read); a finite-to-one extension of an amenable action is amenable |

2. **Every rigidity-transport operation on main preserves amenability.**
   - Products (`quantum-rigidity-is-product-stable`).
   - Deterministic extensions (`deterministic-extensions-of-rigid-sfts-are-rigid`). An extension of an
     amenable action is amenable.
   - Closed invariant subsets. Rigidity passes down by monotonicity of (Q3), and so does amenability.

   So no counterexample can be assembled from the known rigid examples by the known transfers.
3. **The operations that make non-amenable actions of overgroups destroy rigidity.**
   - *Coinduction* is the standard way to push an action of an exact subgroup up to a non-exact
     overgroup. It is never rigid when the double coset space is infinite (Corollary 3 of
     `quantum-rigid-subshifts-cluster-the-modifications-of-each-point`).
   - The *emitter compactifications* of free products carry non-amenable isotropy when the vertex group
     is non-amenable. They are Bowditch-type boundary actions, and they are never rigid
     (`v-stabilized-stabilizer-engines-are-never-finitely-presented`).
   - So the natural non-amenable **boundary** actions in the free-product world fail rigidity. This is
     why the statement is phrased with amenability and not merely with strong proximality: the killed
     examples are convergence actions, hence strongly proximal (recalled), and still non-rigid.
4. **Rigidity mechanisms.** Rigidity on main has exactly three sources:
   - compression toward ends;
   - finite presentation of a boundary host, read backwards;
   - determinism over amenable groups.

   Each produces an amenable action by construction, the first two because the points are ends of
   hyperbolic or building geometry.

## What a counterexample needs, and the cheapest tests

- **A new rigidity source**, one that is not compression toward ends of an amenable boundary.
- **(T1)** A measure-preserving SFT over `F_m × F_n` that is quantum rigid. Codings of irreducible
  lattices in products of trees, as in Mozes's aperiodic tilings (recalled; whether they preserve a
  measure is unchecked), are the natural candidates. Lane bh-g2-buildings already studies Mozes-type
  SFTs.
- **(T2)** Any quantum-rigid SFT over a finitely presented non-exact group, such as a group coarsely
  containing an expander. None is recorded.
- **What the statement cannot touch.** Routes that do not put the input inside the acting group of a
  rigid subshift. There are two recorded ones:
  - the `V`-less stabilizer engines (`boone-higman-via-stabilizer-engines`), which need no rigidity;
  - Track B, where the input sits in units over a fixed scaffold.

  Neither is blocked even if the statement is true.

## Lesson for general BH

The master route inherits an analytic constraint that no combinatorial gate shows.
- Its fp simple group contains `Λ_0 ⊇ G`, so for non-exact inputs the dynamics must be non-amenable.
- Every rigidity mechanism we have manufactures amenable, boundary-type dynamics.
- The constructions that would leave amenability (coinduction, emitters, independent coset data) are
  exactly those that the clustering principle forbids.

So after (IE), the decisive adversarial question for (★′) is this one. Settling it either way changes
the ranking: true confines the master route to exact inputs and promotes the `V`-less engines and Track B; false
gives the first non-amenable rigid dynamics.

## Attempts

**2026-09-18, bh-break (minimal-counterexample): REFUTED** by
`rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer`, through
`non-amenable-stabilizer-from-gluing-a-cone-compactification`. This is a lane proof and is not reviewed.
It supersedes the OPEN line at the top of this node.
- **Cone.** `products-with-z-have-rigid-compactifications-with-fixed-points` works over
  `Λ_0 × Z`. It puts a `C_Z` height, constant along `Λ_0`, and a copy of a rigid compactification of `Λ_0`
  on the `*` slice only. The result is a rigid compactification whose points `±^Z` are fixed by all of
  `Λ_0 × Z`. Rigidity holds because the height letters form a commutative chain, fibre letters on
  different slices are orthogonal, and one slice is a quantum family for `Λ_0`.
- **Glue.** Take `Λ_0 = F_2` and glue with `C_Z` over `(F_2 × Z) * Z`, using
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`. The result is minimal, topologically
  free and rigid. The point whose sink piece carries `+^Z` has stabilizer `F_2 × Z`, which is not
  amenable, so the action is not topologically amenable.
- **Which evidence fails.**
  - Items 2 and 4 miss a transfer: cones over a rigid compactification are rigid, and they manufacture
    global fixed points.
  - Item 3's inference fails: non-amenable isotropy in a free-product compactification does not by itself
    destroy rigidity. The emitters fail for another reason.
- **What survives.** "Rigid minimal topologically free SFT ⇒ exact acting group" is untouched, because
  the counterexample group is exact. The "if true" branch (confinement to exact inputs) no longer follows
  from this node. It would need that exactness statement instead.
