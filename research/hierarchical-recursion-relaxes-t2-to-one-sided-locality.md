---
rg: 2
id: hierarchical-recursion-relaxes-t2-to-one-sided-locality
kind: claim
title: Realizing level-k relators on level-k supertiles (Robinson/Mozes-style recursion) is compatible with the commutator squeeze and leaves the tower law ample room, but collapses by the profinite theorem unless transports read seams of unbounded level; its real gain is that a self-simulating layer can verify transports as computable relations, so T2 needs only ONE-sided locality (local lifts), and the combing obstruction survives there, so the crux becomes a one-sided periodic-orbit coding of a non-exact group
requires:
  - word-codings-of-t2-force-finite-presentation
  - pointer-encodings-give-non-linear-two-sided-locality
  - residual-towers-constrain-non-lie-commutant-layers
  - two-sided-locality-holds-for-matrix-linear-automata
distinct_from:
  word-codings-of-t2-force-finite-presentation: that classifies relator mechanisms in local two-sided encodings; this tests the hierarchical candidate and finds that it relaxes the transport side from local rules to computable relations, rather than being a new relator mechanism on the lift side.
  two-sided-locality-holds-for-matrix-linear-automata: that requires transports given by local rules (its 4(b)-(c)); this shows a self-simulating verification layer removes that requirement, provided the lifted system is the sofic label factor.
---

**Status.**
- Items 1 and 2 follow from landed nodes. Item 1 is elementary arithmetic. Item 2 applies item 4(a) of
  `two-sided-locality-holds-for-matrix-linear-automata` (lane proof, unreviewed).
- Item 3 is a **design statement**, not proved. It relies on the Durand–Romashchenko–Shen fixed-point
  self-simulation (recalled): hierarchical SFTs whose level-`k` computation zones verify an arbitrary
  computable predicate on level-`k` data, and whose projection is exactly the set of configurations
  satisfying it.
- Item 4 is proved from `word-codings-of-t2-force-finite-presentation`, item 1. Item 5 is the new open
  crux.
- Lane bh-ra-t2, 2026-09-19; no priority claimed. **T2 is not built.**

## Statement

1. **The squeeze and the tower law are compatible with recursion.**
   - The layer is a product of finite groups `∏ Q_k`, which is non-Lie. So the commutator squeeze does not
     start.
   - The tower law asks for `ν(Z_1 · K_(>N)) ≥ ψ(R_S · sys(N_N))`.
     - Labels on level-`k` loops of length `ℓ_k ≍ s_k`, the supertile side, give `log I_N ≲ Σ_(k≤N) ℓ_k ≍ s_N`.
     - So `sys(N_N) ≲ s_N`, and under linear repetitivity the right side is `≍ s_N^(-2)`.
     - Seams of level `N + 1` alone occupy density `≍ 1/s_(N+1) ≫ s_N^(-2)`. A seam-sensitive singular set
       has ample room.
   - Recursion puts the short deep kernel elements at the scale of the supertiles they act on, which is
     exactly what the tower law asks.
2. **Recursion alone collapses.** Suppose the level-`k` relator structure and transports are determined by
   the level-`k` supertile and boundedly many levels above it. Then the transports are level-bounded, and by
   item 4(a) of the linear node each label layer is a minimal equicontinuous factor on which the lifts act
   by translations. The lifted group is then abelian.

   So a Robinson/Mozes recursion must be combined with transports that read seam colours of unbounded level.
   Minimality forbids recursion *alone*, not recursion.
3. **The real gain: transports need not be local (design).**
   - In a self-simulating SFT, the level-`k` computation zones can check any computable relation
     `w_(L′) = h(w_L)` between the labels of adjacent level-`k` loops. This works if `h` is computable in the
     zone's time and space budget, polynomial in `s_k`, and it may read seam colours.
   - Let `Y` be the **sofic** factor that forgets the computation layer, as the prefix track `b` was dropped
     in the pointer node.
   - Lifts `φ_γ` act on labels only. If every `h` commutes with the lift action on `O_k`, then `φ_γ`
     preserves the set of label configurations satisfying all relations. That set is `Y`, so
     `φ_γ ∈ Aut(Y)`.
   - Consequence: **two-sided locality relaxes to one-sided locality.** Only right multiplication must be
     given by bounded-radius rules. Left multiplication (the transports) only needs to be computable.
   - Costs:
     - `Y` is sofic, not SFT, so it refutes (RA_free) at best and gives no finitely presented group (scope
       note of `algebraic-rows-carry-rigid-free-commutants-but-never-minimality`).
     - Rigidity of the sofic factor and minimality of `Y` must be checked separately.
4. **The combing obstruction survives the relaxation.** The combing lemma uses only right-multiplication
   locality. So one-sided word codings with bounded end rewriting still force finite presentation, and
   Osajda's infinitely presented groups still have none.
   - The input a one-sided word coding needs is a **finitely presented, residually finite, non-exact**
     group. None is known to us.
     - Higman embedding gives finitely presented non-exact groups, but not residually finite ones.
     - The Kharlampovich–Myasnikov–Sapir finitely presented residually finite groups of arbitrary complexity
       are solvable, hence exact.
   - Of the four known relator mechanisms (`word-codings-of-t2-force-finite-presentation`, item 3), recursion
     adds none on the lift side. The relaxation of item 3 acts on the transport side only.
5. **The sharpened crux (open): a one-sided periodic-orbit coding.** Find a finitely generated group
   `Γ̃ ≤ Aut(B^(Z))`, with the loop decorations as part of the alphabet, and invariant finite sets `X_n` of
   loop-periodic configurations, such that:
   - `Γ̃` acts on each `X_n` regularly, through a finite quotient `Q_n` of one fixed **non-exact** group `Γ`;
   - `Γ` acts faithfully on `⋃_n X_n`.

   The sets `X_n` may be carved out by computable, simulation-checked constraints. Examples:
   - The linear pair and pointer codings satisfy this, with exact `Γ`.
   - Word codings fail it for infinitely presented `Γ` (item 4).

   A positive answer for Osajda's group, plus a computable left-multiplication transport and the design
   checks of item 3, gives T2 for (RA_free)/(RA′). It gives no finitely presented carrier.

## Proof

**1.**
- `I_N ≤ ∏_(k≤N) |Q_k| ≤ ∏_(k≤N) |B|^(ℓ_k)`, and `ℓ_k` grows geometrically.
- `sys(N_N) ≤ (2/h) log I_N + O(1)` (tower node, item 2).
- `ψ(R) ≍ R^(-2)` for linearly repetitive `Z^2` hierarchies.
- The density of cells within bounded distance of level-`(N+1)` seams is `≍ 1/s_(N+1)`.

**2.** This is item 4(a) of `two-sided-locality-holds-for-matrix-linear-automata` verbatim: level-bounded
transports give finite-valued cocycles continuous over the odometer, hence equicontinuous label factors.

**4.** The proof of item 1 of `word-codings-of-t2-force-finite-presentation` never uses the left rules. ∎

## Lesson for general BH

**Hierarchy moves the burden from locality to computability, on one side only.**
- Recursion at the supertile scale is what the tower law wants, but on its own it is profinite and
  collapses. It needs seam-sensitive transports.
- Its genuine contribution is that self-simulation can *verify* transports that no cellular automaton
  *implements*. So the transport side needs only computability, while the lift side must stay local.
- The lift side keeps the combing obstruction. The whole difficulty of T2 is now one-sided: a non-exact
  group acting regularly on loop-periodic configurations through bounded-radius rules.
