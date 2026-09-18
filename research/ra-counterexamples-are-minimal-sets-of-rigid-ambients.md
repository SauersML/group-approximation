---
rg: 2
id: ra-counterexamples-are-minimal-sets-of-rigid-ambients
kind: claim
title: A counterexample to (RA) at a non-exact group is exactly a topologically free minimal subsystem of a quantum-rigid ambient, and it is automatically non-amenable; coset ambients over indivisible homogeneous actions have only fixed points as minimal sets; (RA) does not obstruct the permutational route
requires:
  - quantum-rigidity-passes-to-subshifts
  - cornulier-regime-coset-sfts-are-quantum-rigid
  - group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp
  - decidable-residually-finite-non-exact-group-exists
distinct_from:
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that is the open question (RA); this reduces its negation at non-exact groups to a pure minimal-set question about rigid ambients, kills the permutational (coset) ambients over indivisible actions, and records that (RA) says nothing about non-minimal rigid actions.
  rigid-subshifts-over-free-factors-are-tight-almost-everywhere: that proves (RA) over F_n from the geometry of the tree; this uses no geometry and instead locates where a counterexample could and could not come from.
  group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp: that notes rigid non-amenable coset shifts exist but are not minimal; this proves that for indivisible actions no minimal subsystem of any coset subshift is even infinite.
---

**ESTABLISHED** (lane bh-ra-counter, 2026-09-18; elementary; not reviewed; no priority claimed).
It is progress on `quantum-rigid-minimal-topfree-subshift-actions-are-amenable` ((RA)) from the
constructive side. It does not settle (RA).

## Setting

- `Λ` is finitely generated, `A` a finite alphabet, and "rigid" means `D`-quantum rigid over a field
  `k` for some `D`, as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`.
- A *rigid ambient* is any rigid subshift `X ⊆ A^Λ`.
- For a transitive action `Λ ↷ S = Λ/Δ`, the *coset ambient* is the subshift of right-Δ-invariant
  configurations, identified with `A^S`.

## Theorem

1. **Carving.** `Λ` carries a minimal, topologically free, rigid subshift iff some rigid ambient over
   `Λ` has a minimal subsystem on which `Λ` acts topologically freely.
2. **Non-amenability is automatic at non-exact groups.** If `Λ` is not exact, no action of `Λ` on a
   compact space is topologically amenable. Hence:
   - (RA) fails at `Λ` iff item 1 holds at `Λ`;
   - the weaker form (RA′), "a minimal topologically free rigid subshift forces `Λ` exact", is
     equivalent to: *no rigid ambient over a non-exact group has a topologically free minimal
     subsystem.*
3. **Rigid non-amenable ambients from permutational actions.** Let `Λ` be finitely presented, and
   let `Λ ↷ S = Λ/Δ` be transitive with `Δ` finitely generated and finitely many orbits on `S × S`.
   Every transitive type (A) action is of this kind.
   - Every subshift of the coset ambient `A^S` is rigid (`cornulier-regime-coset-sfts-are-quantum-rigid`).
   - The full coset ambient is topologically free iff every `g ≠ 1` moves infinitely many points of `S`.
   - If `Λ` is not exact, it is a rigid, topologically free, non-amenable action. It is never
     minimal: the constant configurations are fixed points.
4. **Indivisibility obstruction.** Suppose the closure of the image of `Λ` in `Sym(S)` is `Aut(𝕄)` for
   a countable homogeneous relational structure `𝕄` on `S` that is *indivisible*: for every finite
   colouring of `S`, some colour class contains an induced substructure isomorphic to `𝕄`. Then every
   minimal subset of every subshift of `A^S` is a single constant configuration. In particular none is
   infinite, and none is topologically free.
5. **Scope of (RA).** (RA) is about minimal actions only, so it does not obstruct the permutational
   route. If the decidable non-exact group `G` of `decidable-residually-finite-non-exact-group-exists`
   embeds in a finitely presented `Λ` with a transitive type (A) action whose nontrivial elements have
   infinite support, then item 3 gives a rigid, topologically free, non-amenable ambient over `Λ`. That
   is consistent with (RA) holding.

## Proof

1. (⇒) Take the ambient to be the subshift itself. (⇐) A minimal subsystem of a rigid ambient is a
   subshift of it, hence rigid by `quantum-rigidity-passes-to-subshifts`.
2. If `Λ` acts amenably on a compact space `Y`, pick `y ∈ Y`. The orbit map `λ ↦ λy` extends to a
   continuous equivariant map `βΛ → Y`, and amenability pulls back along it, so `Λ ↷ βΛ` is amenable.
   That is exactness of `Λ` (Higson–Roe 2000; Ozawa 2000; Anantharaman-Delaroche, all recalled, not
   re-read). The two equivalences are then item 1 read at non-exact `Λ`.
3. Rigidity is the cited node. Write `(gc)(s) = c(g^(-1)s)`.
   - If `g` has infinite support and `[p]` is a cylinder on a finite `F`, pick
     `s ∈ supp(g) \ (F ∪ gF)`. Then `s` and `g^(-1)s` are distinct and both lie outside `F`. So some
     `c ∈ [p]` has `c(s) ≠ c(g^(-1)s)`, and `gc ≠ c`. Hence `Fix(g)` contains no cylinder.
   - If `supp(g) = E` is finite, every configuration constant on `E` is fixed by `g`, since
     `g^(-1)` preserves `E` and fixes `S \ E`. That is a cylinder inside `Fix(g)`.
   - So `Fix(g)` has empty interior iff `g` has infinite support. Item 2 gives non-amenability, and
     constants are fixed.
4. Let `Y ⊆ A^S` be closed and invariant, and `c ∈ Y`, with the action `(λc)(s) = c(λ^(-1)s)`.
   - By indivisibility, some colour `a` has a colour class containing an induced copy `𝕄′ ≅ 𝕄`.
   - Let `F ⊆ S` be finite. The substructure on `F` embeds in `𝕄`, hence in `𝕄′`, as some `F′ ⊆ 𝕄′`.
   - By homogeneity the partial isomorphism `F′ → F` extends to some `θ ∈ Aut(𝕄)`. Density gives
     `λ ∈ Λ` agreeing with `θ` on `F′`. Then `(λc)|F ≡ a`.
   - So the constant configuration `a` lies in the orbit closure of `c`, hence in `Y`. A minimal `Y`
     is the orbit closure of any of its points, so `Y = {a}`. ∎
5. This is item 3 applied to `Λ`. (RA) quantifies over minimal actions, and the ambient of item 3 is
   not minimal. ∎

## Instances of item 4

Indivisible homogeneous structures, all classical (recalled): the pure countable set, `(Q,<)`, the
dense cyclic order, the random graph, and the generic tournament. So:
- highly transitive actions, including `V` on the dyadic points;
- `F` on the dyadic points of `(0,1)`;
- `T` on the dyadic points of the circle;
- any action dense in the automorphism group of one of these structures

give coset ambients that are rigid and topologically free but can never be carved into a counterexample
to (RA). This makes precise the remark in `group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp`
that the Cornulier-regime shifts are not minimal: for these actions no minimal set is even infinite.

## Calibration

- Over `F_n`, every rigid subshift without isolated points maps onto `∂F_n`
  (`rigid-subshifts-over-free-factors-are-tight-almost-everywhere`). This agrees with item 3: a finitely
  generated infinite-index subgroup of `F_n` has infinitely many double cosets, so `F_n` has no
  Cornulier-regime coset ambient.
- The crossing-wire shift over `Z²` (49939b957a) is a minimal rigid topologically free subshift over an
  exact group. Item 2 makes no claim there.

## What is left open

- **(Q1)** Is there an action `Λ ↷ S` with finitely many orbits on pairs whose coset ambient has an
  infinite, topologically free minimal subset? By item 4 the closure `Aut(𝕄)` must be divisible. For
  oligomorphic actions this is a question about minimal unary expansions of `𝕄`, in the spirit of
  Kechris–Pestov–Todorcevic.
- **(Q2)** Minimal subsets of rigid group subshifts that are not coset shifts, for example
  Ledrappier-type shifts. By `group-subshifts-are-quantum-rigid-iff-the-lamp-group-is-fp` these rigid
  ambients over a non-exact finitely presented `Λ` are exactly finitely presented lamp groups `M ⋊ Λ`
  with `M` an infinite exponent-`p` module. Inflating a module from a quotient makes the kernel act
  trivially, and then no minimal subset is topologically free. So the non-exact part has to act on `M`
  with infinite support.
- **(Q3)** Tight spacetimes (v7), which are neither coset nor group ambients.

## Lesson for general BH

**(RA) is purely a question about minimal sets of rigid ambients.**
- Rigidity is inherited by carving, and non-amenability is automatic at a non-exact group.
- The only rigid non-amenable ambients we know are permutational coset shifts. For every indivisible
  action (Thompson-type, highly transitive, dense orders) they collapse to fixed points under
  minimality.
- That is why every minimal rigid example on main is amenable.

A refutation needs one of two things:
- a rigid ambient whose symmetry is *divisible*;
- a non-permutational ambient: a group shift with the non-exact part acting on the module with
  infinite support, or a tight spacetime.

It also needs a carving that avoids fixed points.

**Correction to the v7 summary.** (RA) does not confine "every track" to exact inputs. It blocks the
minimal-subshift tracks: Track A, its seed versions, and the ring route through minimal groupoids.
The permutational route is untouched. There, a type (A) action of an fp overgroup of the input gives
twisted Brin–Thompson hosts (Belk–Zaremsky) and a rigid non-minimal coset ambient, and (RA) says nothing
against either.

Credits:
- exactness and amenable actions: Higson–Roe, Ozawa, Anantharaman-Delaroche;
- non-exact groups: Gromov, Arzhantseva–Delzant, Osajda;
- permutational wreath products: Cornulier;
- indivisibility of homogeneous structures: Fraïssé, El-Zahar–Sauer and Sauer;
- dynamics of automorphism groups: Kechris–Pestov–Todorcevic;
- type (A) actions and twisted Brin–Thompson groups: BFFHZ and Belk–Zaremsky.

All are recalled, not re-read at source.
