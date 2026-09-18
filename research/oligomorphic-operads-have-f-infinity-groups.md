---
rg: 2
id: oligomorphic-operads-have-f-infinity-groups
kind: claim
title: Conjecture - an operad with transformations whose transformation groups act oligomorphically on its elementary classes, with type F-infinity stabilizers of finite tuples, has operad groups of type F-infinity; this unifies Thumann's theorem, the Röver–Nekrashevych transfer and the twisted Brin–Thompson criterion
requires:
  - thumann-operad-groups-need-only-f-infinity-transformations
  - thumann-finiteness-without-finite-type
  - finite-type-operad-groups-split-over-a-label-kernel
---

**OPEN** (conjecture, lane bh-invent-07, 2026-09-18). Proposed as the operadic finiteness engine for
"programmable" hosts. Parts (a) and (b) of the reduction below are lane sketches, not reviewed; part
(c) is the connectivity gate. No priority claimed.

**Update (2026-09-18, bh-invent-07).** Gate (c) is proved under a splitting condition (G) by
`thumann-finiteness-without-finite-type` (Variant), assuming very elementary classes of bounded
degree. (G) asks that the splitting category of every large elementary class be highly connected.
So the conjecture holds whenever (O1) and (O2) supply cocompactness and stabilizers, which is the
content of the sketches (a) and (b), and (G) holds. Without (G) it stays open.

## Setting

Let `𝒪` be a planar, symmetric or braided operad with transformations. Assume it has finitely many
colors, is color-tame, and satisfies the cancellative calculus of fractions. Unlike Thumann's
setting, the set `E` of elementary transformation classes may be **infinite**. Thumann's
Proposition `07546` shows that `E` is invariant under the right action of the degree-1 operations, so
`Aut_ℐ(c)` acts on the elementary classes with output `c`.

**(O1), oligomorphic finite type.** For each `n`, the one-sided classes of composites of elementary
operations of degree at most `n` fall into finitely many `ℐ`-orbits.

**(O2), stabilizers.** For each such composite `θ`, the pull-through subgroup
`H_θ = Stab([θ]) ≤ Aut_ℐ(c)` is of type `F_∞`, and so are finite intersections of its conjugates.
Each `Aut_ℐ(c)` is `F_∞`. For an `F_n` version, read `F_n` throughout.

**Conjecture.** Under (O1) and (O2), `π_1(𝒪, X)` is of type `F_∞`, respectively `F_n`.

## Instances

1. **`E` finite.** (O1) is Thumann's finite type. (O2) holds as soon as `ℐ` is `F_∞`, since the
   stabilizers have finite index. This is `thumann-operad-groups-need-only-f-infinity-transformations`,
   so the conjecture holds here.
2. **Röver–Nekrashevych.** `E` is a single class, and `ℐ = G` is self-similar and `F_∞`. This is a
   special case of 1, recovering Skipper–Zaremsky's theorem.
3. **Twisted Brin–Thompson `SV_G`.**
   - `E` is the set of coordinate splits `{θ_s : s ∈ S}`, and `ℐ = G` acts by `θ_s * g ≈ θ_{g(s)}`.
   - (O1) says `G` has finitely many orbits on `k`-subsets of `S` for every `k`, i.e. it is
     oligomorphic.
   - (O2) says the stabilizers of finite subsets are `F_∞`.
   - Together these are type `(A_∞)`. There the conjecture is the Belk–Zaremsky criterion (their
     Conjecture H), which is claimed on main by `twisted-brin-thompson-type-fn-criterion`
     (bh-typeA-universal; referee a PASS, second pass pending).

## Reduction (what is proved, what is open)

Thumann's proof has three parts: Brown's criterion applied to `Γ ↷ 𝒰/𝒢`, with the degree filtration.
1. **(a) Finitely many `Γ`-orbits of cells in each `(𝒰/𝒢)_n`.**
   - Repeat the surjectivity argument (arXiv:1409.1085, l.3814–3833), with the finite set `S`
     replaced by a set of `ℐ`-orbit representatives of elementary operations.
   - The pull-through step (Observation `37111`) moves every elementary operation at the root into
     the orbit of a representative.
   - Lower levels are normalized modulo input transformations, which `𝒰/𝒢` divides out.
   - (O1) then bounds the number of orbits of cells.
   - Lane sketch.
2. **(b) Cell stabilizers are `F_∞`.** Thumann's proposition (l.3700–3781) needs exactly the groups
   `H_θ` and finite intersections of their conjugates, so this is (O2). Lane sketch.
3. **(c) Connectivity of descending links tends to infinity with degree. PROVED under (G)**
   (`thumann-finiteness-without-finite-type`); open without it.
   - Thumann's core/corona argument uses a bound on the degrees of elementary classes only once, in
     the corona estimate. The core already allows infinitely many archetypes.
   - With infinitely many classes, a descending link is a "colored" arc complex: each merge carries a
     class from `E`, and the merges must be jointly realizable.
   - Thumann's arc complex theorem already handles such colorings: its archetype sets may be
     infinite. What infinitely many classes add is the splitting of large elementary classes, and
     that is exactly condition (G).
   - For `SV_G`, (G) is the grid-sphere computation (`stein-complex-elementary-intervals-are-grid-spheres`).

## Why it matters (programmable hosts)

By `finite-type-operad-groups-split-over-a-label-kernel`, a finite-type operad cannot compile a
non-residually-finite input through its transformations. The only escape from that dichotomy is an
infinite `E` permuted oligomorphically by `ℐ`.

The operadic form gives two freedoms beyond `SV_G`:
- **Elementary moves need not be coordinate splits.** They can be operations of different arities and
  shapes, including "machine moves".
- **Relations among moves become part of the host.** They are the strictly elementary classes
  (minimal common refinements). So they can be designed, not just inherited from the combinatorics of
  cube cutting.

A **programmable host** is then specified by three pieces of data:
- a finitely presented decidable group `ℐ ⊇` the input;
- an oligomorphic `ℐ`-set `E` of moves with `F_∞` finite-tuple stabilizers;
- a finite table of how pairs of moves refine.

Finiteness follows from the conjecture, and simplicity follows as for `SV_G` when some relation twists
shapes (killing the shape group).

The remaining content of general BH is then an **operadic actor problem**: find such a table for the
canonical inputs `H_Γ` of `decidable-host-classes-reduce-to-canonical-kazhdan-groups`. It is strictly
more flexible than asking for a type `(A)` action on a bare set, because moves may carry relations
that a bare permutation action cannot express.

## Lesson for general BH

- **Unification.** The three finiteness engines behind today's hosts (Thumann cube operads, the
  Röver–Nekrashevych transfer, twisted Brin–Thompson) are instances of one statement: finitely many
  transformation orbits on move-tuples, plus `F_∞` stabilizers.
- **Where complexity must go.** The finite-type case is capped to the residually finite part. So
  complexity must enter through the oligomorphic infinite set of moves, and the actor problem is the
  design of that set together with its refinement table.
