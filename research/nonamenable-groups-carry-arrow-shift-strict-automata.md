---
rg: 2
id: nonamenable-groups-carry-arrow-shift-strict-automata
kind: claim
title: Every nonamenable group carries a strict fibre automaton over a fixed-point-free arrow shift
distinct_from:
  gottschalk-surjunctivity-conjecture: that asks for a strict automaton on a full shift; this builds strict maps only over a shift of finite type with no finite orbits, and shows that no full shift maps equivariantly into that base.
  split-decoders-have-generic-cantor-fibers: that describes the fibres of a split cellular map on a full shift; this constructs strict maps fibred over an arrow shift and records why they cannot be pulled back to a full shift.
artifacts:
  - research/artifacts/ideas-gottschalk-2-2026-09-14.md
---

Let `G` be a countable group acting on configuration spaces by
`(g.x)(h) = x(g^(-1) h)`, and let `A` be a finite alphabet with at least two
letters.

For a finite `S <= G` with `e in S` and `S = S^(-1)`, the **arrow shift** is

```text
X_S = { φ in S^G : for every h in G there are at least two g with g φ(g) = h }.
```

It is a `G`-invariant shift of finite type, with window `S^(-1)`. For `φ` in
`X_S` write `f_φ(g) = g φ(g)`.

**Theorem.**
1. **Nonemptiness.** `G` is nonamenable iff `X_S` is nonempty for some such `S`.
   If `G` is amenable, then `X_S` is empty for every `S`.
2. **The hotel map is strict.** For every `S`, the map
   `Φ(φ, x) = (φ, x∘f_φ)` is a block map on `X_S × A^G`. On every fibre it is
   injective and not surjective. So `Φ` is injective and, when `X_S` is
   nonempty, not surjective.
3. **No finite orbits.** No point of `X_S` has a finite `G`-orbit. In
   particular `X_S` has no `G`-fixed point.
4. **No full shift maps in.** There is no `G`-equivariant map, continuous or
   not, from any full shift `B^G` into `X_S`. The same holds for every `G`-set
   with a finite orbit.

**What this does and does not say.**
- Every nonamenable group carries a Hilbert-hotel automaton that is strict over
  a nonempty base of finite type.
- A Gottschalk counterexample on a full shift cannot be obtained by pulling
  this back along an arrow field computed from the data. By (4), any such
  computation has to fail on symmetric configurations, and the automaton would
  have to absorb the defect there.
- It proves nothing about the full-shift conjecture itself. Free groups are
  sofic, and they carry these hotels.

The route is `arrow-shift-strict-automata-proof`. It is elementary:
- Følner's criterion;
- Marshall Hall's theorem on distinct representatives for families of finite
  sets;
- a preimage count on finite coset spaces.

The bounded-displacement doubling characterization of nonamenability is
classical (Deuber–Simonovits–Sós; Whyte). This lane did not re-pin those
sources, and the route does not depend on them.
