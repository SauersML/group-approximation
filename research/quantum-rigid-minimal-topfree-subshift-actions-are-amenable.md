---
rg: 2
id: quantum-rigid-minimal-topfree-subshift-actions-are-amenable
kind: claim
title: Every minimal, topologically free, quantum-rigid subshift action of a finitely generated group is topologically amenable (open); if so, the master route's object (★′) exists over no non-exact group and cannot reach Osajda's decidable non-exact group
requires:
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - decidable-residually-finite-non-exact-group-exists
distinct_from:
  exactness-separates-boone-higman-iff-fp-simple-groups-exact: that shows Boone–Higman forces a finitely presented simple non-exact group; this asks whether the master route's rigid dynamics can ever be non-amenable, which that group would need if it came from this route.
  amenable-groupoid-full-groups-are-exact: that asks whether full groups of amenable groupoids are exact; this asks whether quantum rigidity forces the transformation groupoid to be amenable in the first place.
  master-route-needs-only-topological-freeness: that reduces the route to (★′); this is the analytic obstruction to (★′) that no current tool rules out.
---

**OPEN.** Posed by lane bh-star-b, 2026-09-18, as the adversarial form of (★′). No claim is made
either way; the evidence is below. Partial results are in the section "Progress" at the end.

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

1. **Every proved minimal, topologically free rigid example is amenable.** Minimality matters, though. The rigid full
   coset shifts of the Cornulier regime (`cornulier-regime-coset-sfts-are-quantum-rigid`, for example Thompson's `V`
   on the dyadic points) are topologically free and carry Bernoulli measures, so their actions are **not** amenable.
   They are not minimal: constant points are fixed.

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

## Progress (bh-star-b, 2026-09-18, later)

- **(RA) holds over free groups.** Over `F_n` (`n >= 2`), every quantum-rigid subshift without
  isolated points factors continuously and equivariantly onto `∂F_n`, so its action is topologically
  amenable. Minimality and topological freeness are not needed.
  - Over `Λ_0 × F_n`, an invariant probability measure lives on points determined by one thick slab.
  - The mechanism: in a rigid subshift, the free branches of nested slabs converge to an equivariant
    end, and `∂F_n` carries no invariant measure.
  - Source: `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`.
- **Test (T1) is answered: the Mozes-type candidates are not rigid.** Two families fail:
  - the covering-map SFT of a complete square complex, which is `Γ\Aut(T_1 × T_2)`;
  - its algebraic homogeneous subshifts `Γ\(PGL_2(Q_p) × PGL_2(Q_l))`.

  Both are measure-preserving over a reducible lattice. The reason is that compact stabilizers of slab
  states rotate every branch at once (`tree-lattice-homogeneous-subshifts-are-not-quantum-rigid`).
- **What is left of (RA)** splits into three parts:
  - over `Λ_0 × F_n`: *tight* spacetimes, determined by one slab and carrying an invariant measure, or
    non-amenable actions with no invariant measure;
  - over groups with no free direct factor (for example one-ended Kazhdan `Λ_0`): open;
  - (T2), rigid subshifts over non-exact groups: open.
- **Tight spacetimes and algebraic dynamics** (`group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp`).
  - For group subshifts, quantum rigidity is equivalent to finite presentation of the lamp group.
  - Over `Λ_0 × F_n`, rigid group subshifts are uniformly tight spacetimes.
  - Every finitely presented lamp group over a non-amenable `Λ` is a rigid, measure-preserving,
    non-amenable action, and never a minimal one. So the hypothesis *minimal* carries the whole content
    of (RA).
- **One-ended groups.** Over one-ended non-amenable groups the only recorded non-boundary rigidity is
  the Cornulier regime, and there (IS) makes every minimal set a fixed point for `V`, `F`, `T` and
  `CT_P(Z)`.
  - So a counterexample to (RA) over a one-ended group would be a positive answer to
    `finite-double-coset-space-with-free-minimal-coset-sft` whose action is not amenable.
  - That would need, for instance, a non-exact group in the Cornulier regime.
  - Conversely, (RA) implies that every positive answer to that question lives over an exact group.
