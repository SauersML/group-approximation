---
rg: 2
id: z-semilocalized-embeds-in-fp-rf-group
kind: claim
title: For some finite set S of primes, the group Z_(S) of rationals with denominators prime to S embeds in a finitely presented residually finite group
distinct_from:
  z-localized-embeds-in-fp-rf-group: that asks it for one prime, S = {l}, and implies this; this is the weakest cofinite-divisibility form, the one every Bux-Llosa Isenrich-Wu host of an input containing (Q,+) needs.
  end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups: that proves the necessity (its parts 5 and 6); this states the open target on its own and records what excludes it.
---

**OPEN** (stated by lane bh-gln-tracka, 2026-09-18). No witness and no refutation are known.

## Statement

**(SL)** There are a finite set `S` of primes, a finitely presented residually finite group `Λ` and an injective
homomorphism `(Z_(S), +) -> Λ`. Here `Z_(S)` is the ring of rationals whose denominators are prime to every
`p ∈ S`.

## Relations to other statements

- **Monotone in `S`.** If `S ⊆ S'` then `Z_(S') ⊆ Z_(S)`. So (SL) for `S` gives (SL) for every finite `S' ⊇ S`, and
  (SL) holds as soon as it holds for all large `S`.
- **Implied by the one-prime form.** `z-localized-embeds-in-fp-rf-group` is the case `S = {l}`, so it implies
  (SL). The converse is not known. Adding the finitely many missing roots (`q ∈ S ∖ {l}`) by amalgamating with
  `BS(1,q)` over a cyclic group is finitely presented, but residual finiteness is not automatic.
- **Needed by the BLIW method for divisible inputs.** Every group acting faithfully and cocompactly on a locally
  finite tree with finitely presented edge stabilizers and containing `(Q,+)` has an (SL) witness among its vertex
  stabilizers (`end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups`, part 5). This covers every
  BLIW host of `GL_n(Q)`, `Aff(Q)`, `U_3(Q)` or `(Q,+)`, the Hecke route through `SL_2(Q)` among them.

## What a witness `Λ` cannot be

- **Linear.** An element of infinite order of a finitely generated linear group has roots at only finitely many
  primes (`fg-linear-groups-have-roots-at-finitely-many-primes`), while `1 ∈ Z_(S)` has roots at every prime outside
  `S`.
- **Metabelian.** There is the derived-subgroup version of the same bound
  (`fg-metabelian-groups-have-roots-at-finitely-many-primes`). The image of `Z_(S)` in the finitely generated
  abelianization is finite, since a group divisible by infinitely many primes has only torsion image there. So a
  finite-index subgroup `m Z_(S) ≅ Z_(S)` lies in the derived subgroup.
- **A Kharlampovich–Myasnikov–Sapir group.** Their torsion-free subgroups are free abelian of finite rank
  (`kms-minsky-groups-contain-no-z-localized`).
- **Built from non-witnesses by locally finite splittings.** A residually finite `π_1` of a finite graph of groups
  with finite-index edge inclusions that contains `Z_(S)` has a vertex group containing `Z_(S')`, where `S'` adds
  the primes up to the valence (`end-shift-codings-of-q-inputs-need-fp-rf-semilocal-vertex-groups`, part 6).
  - Finite valence has a finite prime budget
    (`bounded-valence-trees-scale-only-primes-below-the-valence`).
  - So only splittings over edge groups of infinite index can create the divisibility, as ascending unions along a
    ray.

**Finite quotients.** A finite-index subgroup of `Z_(S)` has the form `m Z_(S)` with `m` an `S`-number. So in every
finite quotient of `Λ` the image of `1 ∈ Z_(S)` has order an `S`-number, and its closure in the profinite completion
is a quotient of `∏_(p∈S) Z_p`.

**Where the divisibility can come from.** Prime-by-prime devices give only finitely many primes each, within any
finite presentation:
- HNN letters `t a t^(-1) = a^m`;
- valence of trees;
- scalings of self-similar actions, where adding a rational `S`-adic integer on the `m`-ary tree with `m = ∏S` is
  finite-state, but finitely many affine maps of this kind generate a finitely generated subgroup of `Aff(Q)`,
  which is linear and hence excluded. Non-affine finite-state maps are untested.

The one device on main that inverts all integers prime to a given set by a finite presentation is a ring relation.
It is the resolvent relation `A(N+1) = 1` with `N` a counting operator (`leavitt-resolvent-ring-is-fp-and-contains-q`).

## Attempt 1 (lane bh-gln-tracka): the semilocal form does not dodge the K_2 obstruction of the ring routes

The ring routes of `z-localized-embeds-in-fp-rf-group` (attempts 3–9 there) meet one obstruction: tame symbols of
the inverted scalars survive in `K_2` of the host ring, and they must die in finite quotients.
- Replacing `Z_(l)` by `Z_(S)` does not change this. The localization sequence
  `K_2(Z_(S)) -> ⊕_(q ∉ S) K_1(F_q) -> K_1(Z) -> K_1(Z_(S))` has an injective last map
  (`{±1} -> Z_(S)^×`), so `K_2(Z_(S))` surjects onto `⊕_(q ∉ S) F_q^×`. That group is infinitely generated for every
  finite `S`. (This is the localization sequence for `Z ⊆ Z_(S)`; standard, recalled, not re-read.)
- So every host ring that contains `Z_(S)` as a corner, and whose `K_2` detects the corner (as
  `resolvent-ring-corner-symbols-survive-in-k2` shows for `R_l`), carries infinitely many independent tame symbols,
  exactly as in the one-prime case.
- **Verdict.** On the ring side (SL) is no easier than `z-localized-embeds-in-fp-rf-group`. Its advantage is only
  on the necessity side: it is what the BLIW method provably needs.

## Lesson for general BH

Cofinite divisibility, meaning roots at all but finitely many primes, is the arithmetic core that every tree-type
host of a divisible input must already contain in a finitely presented residually finite vertex group.
- Every combinatorial device checked here (HNN letters, tree valence, affine self-similar scaling) contributes
  finitely many primes per finite presentation.
- Rings contribute all primes at once, but pay in `K_2`.

So the open question is sharply: can a finitely presented residually finite group invert all but finitely many
primes without a ring whose `K_2` records each inverted prime?
