---
rg: 2
id: kun-thom-clifford-cover-nonsurjunctive
kind: claim
title: Some Kun--Thom Clifford cover is not surjunctive
root: true
distinct_from:
  kun-thom-nonsofic-wreaths-are-surjunctive: that proves the Kun--Thom wreath W surjunctive; this asks whether its central Z/2 cover E_S fails surjunctivity.
  finite-normal-subgroups-do-not-affect-surjunctivity: that is the universal closure statement for finite normal subgroups; this would refute it on one explicit central extension.
  leavitt-unit-group-nonsurjunctive: that seeks a counterexample on a simple Leavitt host; this seeks one on a weakly sofic central extension of a surjunctive group.
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

**OPEN.** For the Kun--Thom Theorem E pair and some `G`-invariant graph `S` on `X = G/Gamma`, the Clifford
cover `E_S = Vtilde_S semidirect G` of `kun-thom-clifford-cover-weakly-sofic` carries an injective,
non-surjective cellular automaton over a finite alphabet.

Payoff: `E_S` would refute Gottschalk's conjecture. Its quotient `E_S/<eps> = W` is surjunctive, so it
would also refute `finite-normal-subgroups-do-not-affect-surjunctivity`, on a weakly sofic host.

Marked `root` because it heads a counterexample lane of its own.

## Attempts

- **Permanence cannot reach it.** `kun-thom-clifford-cover-has-no-finitary-site-structure`:
  the finitary split-extension theorem does not apply. For the complete graph,
  `complete-graph-clifford-cover-center-dies-in-finite-quotients`: the separated finite-normal theorem
  does not apply either.
- **Linear case.** `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring` reduces it to direct
  finiteness of the Clifford skew group ring `A_S`
  (`clifford-cover-anti-half-skew-ring-not-directly-finite`).
- **Nonlinear case.** Not attempted yet. Any strict automaton must fold its Garden of Eden on
  sofic-invisible elements, and `eps` is invisible to every finite quotient.
- **Surjunctive direction, via local embeddings (observation from w3-products, checked here).**
  - E_S is surjunctive if every finite piece of E_S embeds as an injective partial multiplication table
    into W x F with F finite and eps sent to (1, f0), f0 != 1. W x F is surjunctive
    (products-with-lef-factors-preserve-surjunctivity), and strict tables transfer to realizations.
  - The W-coordinate already carries the site action exactly. So the F-coordinate needs only the sign:
    a finite extraspecial group on the window's sites, with each group element acting by a permutation
    of those sites.
  - Exactness of the table forces those permutations to compose exactly on the whole window. That is an
    exact finite model of the coset action on the window.
  - By coordinate-action-not-sofic, such models cannot exist for all windows, so this proves nothing
    uniformly.
  - It stays live for any specific strict pair whose tables need only a window that admits an exact
    finite model. So a counterexample on E_S needs tables whose window has no exact finite model of the
    coset action.
- **The binary linear case is dead.** This is w3-deligne's p-subgroup argument from its Deligne artifact, re-derived here.
  - In characteristic 2 the kernel of `F_2[E_S] -> F_2[W]` is `(1 + eps) F_2[E_S]`, and it squares to zero, since `eps` is central and `(1 + eps)^2 = 0`.
  - Direct finiteness lifts modulo a nilpotent ideal at every matrix size: if `b a = 1` modulo `J`, then `b a` is invertible.
  - `F_2[W]` is stably finite, so `F_2[E_S]` is too.
  - So no binary Kaplansky pair exists on `E_S`. Linear counterexamples there can live only in odd characteristic, in the anti-central factor.
- **Nonlinear case: orbital localization** (lane w4-clifford-nonlinear, artifact
  `clifford-cover-orbital-localization-2026-09-12.md`).
  - **The filter.** A strict pair reads adjacency on finitely many site pairs. Suppose one finite quotient
    `K\X` separates every read edge from the read non-edges. Then the pair transfers, with the same
    coordinates, to the cover over the graph pulled back from `K\X`. That cover is separated and hence
    surjunctive. So every witness reads a profinitely invisible adjacency
    (`clifford-cover-strict-pairs-read-invisible-adjacency`).
  - **Complete graph, Kun--Thom pair.** The witness's products must force a holonomy subgroup at some read
    site whose profinite closure contains the difference of two read sites. Those two sites lie in one fibre
    of `G/Gamma -> G/Gammabar` (`infranormal-subgroups-have-normal-profinite-closure`).
    - The radical-phase table is such a configuration: moves by `Gamma` at `o` and the path
      `o -> t o -> gamma t o -> h o`.
    - So a witness must contain the Kun--Thom phase pattern, which is also where nonsoficity lives.
  - **Binary alphabets add three screens.**
    - `F_2[E_S]` is stably finite, so the pair is non-formalizable at every stabilization.
    - Some decoder monomial violates the disjoint-footprint condition.
    - The decoder memory is nonamenable.
  - **Where it stops.** No design meeting all four conditions is known. The phase pattern supplies
    invisibility, but no mechanism for non-surjectivity.
- **Surjunctive side: graphs already settled** (same artifact).
  - **Separated covers.** The center survives a finite quotient exactly for finite-pullback graphs
    (`clifford-cover-center-separable-iff-graph-is-finite-pullback`).
  - **Saturated covers.** Covers over profinitely saturated graphs are surjunctive
    (`profinitely-saturated-clifford-covers-are-surjunctive`). This includes the cross graph over the Kun--Thom
    pair, whose center lies in the finite residual.
  - **Where a counterexample can live.** Only on non-saturated graphs: the complete graph, every graph
    carrying the radical-phase edge, and every finite-degree graph (artifact Remark 4.1).
