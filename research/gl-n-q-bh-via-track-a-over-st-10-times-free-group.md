---
rg: 2
id: gl-n-q-bh-via-track-a-over-st-10-times-free-group
kind: route
title: GL_n(Q) into a finitely presented simple group by the group-side master route over the acting group St_10(R_L) x F_2, which needs no Clapham envelope and no squaring; what remains is M2 for St_10(R_L), minimal product simulation, rigidity and E3'
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - gl-n-q-all-n-in-st-10-of-resolvent-ring
  - steinberg-groups-of-r-l-are-quasisimple
  - master-route-needs-only-topological-freeness
  - decidable-fp-groups-have-effective-minimal-free-subshifts
  - nonamenable-products-have-minimal-sft-extensions-of-free-inputs
  - v-times-rigid-topologically-free-sft-full-groups-are-fp
  - bounded-valence-trees-scale-only-primes-below-the-valence
distinct_from:
  gl-n-q-bh-via-leavitt-resolvent-units: that route puts GL_n(Q) in units of a Leavitt-resolvent ring and is dead; this puts St_10(R_L) in the ACTING group of a groupoid host, where the divisible part rides on the acting group.
  gl-n-q-bh-via-steinberg-shell-envelope: that asks for a finitely presented shell envelope of St_N(R_L); this uses St_10(R_L) x F_2 as the acting group of the master route and needs no envelope.
  boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts: that is the ring-side master route for all inputs; this instance avoids its K-gate, which is out of reach for every overgroup of GL_n(Q) (see "Why the group route").
---

**Route** (lane bh-gln-tracka, 2026-09-18). **OPEN.** It is an instance of Track A of the master route
(`research/artifacts/gq-bh-synthesis-master-route.md`, v5 16bd19b7f). For `GL_n(Q)` it removes two steps of Track A,
supplies the non-minimal half of (★′), and pins down the gates that remain.

## The acting group

Let `Λ_0 = St_10(R_L) × F_2`.
- **It contains every `GL_n(Q)`** (`gl-n-q-all-n-in-st-10-of-resolvent-ring`), with image meeting the centre of
  `St_10(R_L)` trivially (`steinberg-groups-of-r-l-are-quasisimple`, item 4).
- **It is finitely presented** (Krstić–McCool / gq-referee-c, recorded on `gl-n-q-explicit-natural-fp-overgroup`).
- **It has solvable word problem** (`leavitt-resolvent-k2-stability-holds`, item 4, for `St_10(R_L)`; `F_2` and
  products are clear).
- **Both factors are finitely generated and non-amenable.** `St_10(R_L) ⊇ GL_2(Q) ⊇ F_2`.

## Steps

1. **No Clapham envelope and no squaring.** Track A embeds a general input `G` in `G × F_2`, then in a Clapham
   envelope `Λ_1`, and works over `Λ_1 × Λ_1` to reach the Barbieri–Sablik–Salo (BSS) product theorem. For
   `GL_n(Q)` the explicit group `Λ_0` is already an fp product of two finitely generated non-amenable groups with
   solvable word problem.
2. **A strongly aperiodic SFT on `Λ_0` (supplied).**
   - BSS Theorem `thm:selfsimulation` makes every product of two finitely generated non-amenable groups
     self-simulable.
   - Corollary `cor:stronglyaperiodic` then gives a self-simulable group with decidable word problem a strongly
     aperiodic SFT.
   - Both were read at source in `research/artifacts/gq-bh-bh-g1-simulation.md`, §1.
   - So `GL_n(Q)` lies in an explicit fp group with solvable word problem carrying a free SFT. Isotropy is trivial,
     so the torsion of `GL_n(Q)` causes no trouble.
3. **Minimality reduces to one group.** Suppose `Y_1` is an effectively closed, minimal, free subshift on
   `St_10(R_L)`, i.e. (M2) for `St_10(R_L)`. Let `Y_2` be one on `F_2`, which exists because `F_2` is effectively
   residually finite (`effectively-rf-groups-have-effective-minimal-free-subshifts`). Then the product coding
   `x(γ_1, γ_2) = (y_1(γ_1), y_2(γ_2))` is an effectively closed subshift on `Λ_0`, and:
   - it is minimal, since the orbit of `(y_1, y_2)` is `St_10(R_L)·y_1 × F_2·y_2`;
   - it is free, since `Stab(y_1, y_2) = Stab(y_1) × Stab(y_2)`;
   - it is effective, by the rules "first coordinate independent of `γ_2`, second independent of `γ_1`" plus the
     effective lists of `Y_1` and `Y_2`, with solvable word problem.

   With `nonamenable-products-have-minimal-sft-extensions-of-free-inputs` for `Γ_1 = St_10(R_L)` and `Γ_2 = F_2`,
   this gives a minimal free SFT on `Λ_0`.
4. **Rigidity.** That SFT, or another minimal topologically free SFT on `Λ_0`, must be quantum rigid. Together with
   step 3 this is (★′) for `Λ_0`.
5. **Group-side finite presentation (E3′).** Apply `v-times-rigid-topologically-free-sft-full-groups-are-fp`,
   which is P2′ for topologically free SFTs. Its layer P2′b is dynamics-free and does not see the input. The
   master route then makes `A(G_V × Λ_0 ⋉ X)` finitely presented, simple and of type (A), and it contains
   `Λ_0 ⊇ GL_n(Q)` (`master-route-needs-only-topological-freeness`, group route).

## Gate map for this `Λ_0`

| gate | status here | why |
|---|---|---|
| Clapham, square | not needed | step 1 |
| free SFT (non-minimal E1) | supplied | step 2 (BSS) |
| (M2) | **open: (M2) for `St_10(R_L)` suffices** | step 3 |
| minimal product simulation | open, same as the general case | `nonamenable-products-have-minimal-sft-extensions-of-free-inputs` |
| rigidity | open: gate 3 (programmable) or (IE) | see "Rigidity" |
| (K′) | **abandoned** | see "Why the group route" |
| E3′ / P2′b | open, input-free | step 5 |

### Constraints on the (M2) witness for `St_10(R_L)`

- **Not almost automorphic.** `St_10(R_L)` is minimally almost periodic. It is perfect with `St_10(R_L)/Z ≅ PE_10(R_L)`
  finitely generated, infinite and simple (`steinberg-groups-of-r-l-are-quasisimple`), and
  `fg-infinite-simple-groups-are-minimally-almost-periodic` applies to that quotient.
  - Let `ρ: St_10(R_L) → C` be a homomorphism to a compact group, with `D` the closure of `ρ(Z)`. `D` is central in
    the closure of the image, so the induced map `PE_10(R_L) → C/D` is trivial.
  - So `ρ` has abelian image, and it is trivial because `St_10(R_L)` is perfect.
  - By `simple-subgroups-act-trivially-on-equicontinuous-factors`, parts 1–3, `St_10(R_L)` then acts trivially on
    the maximal equicontinuous factor of every minimal `Λ_0`-system. So no almost automorphic system (Toeplitz,
    Sturmian or cut-and-project type) and no almost-automorphic coupling can be the witness.
- **No tree skeleton.** `St_10(R_L)` is Kazhdan, so it has (FA) (`decidable-fp-groups-have-effective-minimal-free-subshifts`,
  item 5).

So the witness needs a free minimal effective dynamics of a Kazhdan, minimally almost periodic group with no
equicontinuous or tree structure. That is the general (M2) gate for a Kazhdan input with no finite quotients
(`decidable-fp-groups-have-effective-minimal-free-subshifts`, item 5), and `GL_n(Q)` makes it no easier.

### Rigidity

Both cheap rigidity mechanisms of synthesis v5 are closed for this input.
- **Compression codings** need tree or hyperbolic geometry carrying the input.
  - By `gl-n-q-fixes-a-vertex-in-free-splittings` and `bounded-valence-trees-scale-only-primes-below-the-valence`,
    a coding by a finite graph of groups with finite-index edge groups puts divisibility by every prime above the
    valence into a vertex group, and one with trivial edge groups puts all of `GL_n(Q)` at one vertex.
  - In both cases a compression coding carries the divisible part of `GL_n(Q)` only inside a vertex group, where the coding
    problem recurs for the same input, or at an infinite emitter, which is gate (IE) (in full for free splittings,
    where the whole of `GL_n(Q)` fixes one vertex).
- **The proved (★′) instances** (`F_m × F_n`, tree products, `Ã_2` lattices) act properly on CAT(0) complexes, and
  none contains `GL_n(Q)` (`proper-semisimple-cat0-groups-contain-no-gl-2-q`).
- **fp certification** (`topologically-free-subshift-full-groups-force-quantum-rigidity`) presupposes an fp host,
  which is the target.

So rigidity for 5.3(5) comes from gate 3 (programmable, determinism-type rigidity along the BSS grids of step 2) or
from (IE). Nothing in `St_10(R_L)` shortcuts either.

### Why the group route

(K′) asks for a Farrell–Jones instance for the acting group. Every overgroup of `GL_n(Q)` contains `(Q,+)`, so it is
not residually finite, not hyperbolic, and not CAT(0) in the proper semisimple sense.
- Not residually finite: `(Q,+)` has no finite quotients.
- Not hyperbolic: abelian subgroups there are virtually cyclic.
- Not CAT(0): `proper-semisimple-cat0-groups-contain-no-gl-2-q`.

This excludes `Λ_0`, and every subgroup of a finite product of such groups, from the standard classes for which
Farrell–Jones with coefficients is proved, as far as recalled: hyperbolic and CAT(0) groups, lattices and
S-arithmetic groups (residually finite), mapping class groups and `Out(F_n)` (residually finite), and solvable
groups (`GL_n(Q)` is not solvable for `n >= 2`). The list is context only, not re-read.

So (K′) for any `Λ_0 ⊇ GL_n(Q)` would need an inheritance theorem (through tree actions, extensions or colimits)
or a new Farrell–Jones theorem. The group route needs no K-theory, which is why
this route takes it.

## Status of the premises

- **Established:** steps 1–2 (given the cited nodes and BSS, read at source by bh-g1-simulation); the reductions in
  step 3; the two filters.
- **Open:**
  - (M2) for `St_10(R_L)`;
  - `nonamenable-products-have-minimal-sft-extensions-of-free-inputs`;
  - quantum rigidity in step 4;
  - `v-times-rigid-topologically-free-sft-full-groups-are-fp`.

## Lesson for general BH

For an input with an explicit finitely presented overgroup that contains `F_2`, Track A needs neither a Clapham
envelope nor a square: the overgroup times `F_2` is already a BSS product, so a free SFT comes for free, and the
minimal version reduces to (M2) for the overgroup alone.

What such an input cannot buy is rigidity or a K-gate:
- divisibility, like (T), pins the input to vertices of every tree coding;
- non-residual-finiteness puts every overgroup outside the known Farrell–Jones classes.

For `GL_n(Q)` the decisive open object is one free, minimal, effective subshift on the quasisimple Kazhdan group
`St_10(R_L)`, with no equicontinuous or tree structure. It is the same object as the general (M2) gate, but on one
explicit group.

## Update (2026-09-18, from bh-g1-simulation; design-level, unreviewed)

The (M2) row of the gate map can move to the free product `St_10(R_L) * Z`, which is finitely presented, has solvable
word problem and contains every `GL_n(Q)`:
- `decidable-groups-carry-flexible-free-subshifts` gives every finitely generated group with decidable word problem,
  `St_10(R_L)` included, a free subshift with decidable language, separated gluing and computable points. It is
  transitive, not minimal, and neither almost automorphic nor tree-based, so it passes both filters above.
- `free-products-with-z-inherit-m2-from-decidable-free-subshifts` then gives (M2) on `St_10(R_L) * Z`.
- `free-effective-minimal-subshifts-lift-to-minimal-sfts-times-z2` lifts it to a minimal free SFT on
  `(St_10(R_L) * Z) × Z^2`. That replaces the minimal product-simulation row.

With `Λ_0 = (St_10(R_L) * Z) × Z^2`, the open rows for 5.3(5) are therefore rigidity (now the Z² gate 3, with no
compression shortcut) and E3′. bh-g1-simulation flags lemma (E) of `identifier-markers-give-decidable-free-subshifts`
as the review-critical step.
