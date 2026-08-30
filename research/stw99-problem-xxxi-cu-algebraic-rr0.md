---
rg: 2
id: stw99-problem-xxxi-cu-algebraic-rr0
kind: claim
title: Algebraic Cuntz semigroups detect real rank zero in simple stably finite algebras (STW Problem XXXI)
root: true
artifacts:
  - research/artifacts/stw99-rr0-cluster-2026-08-30.md
---

**Problem XXXI of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  If
`A` is simple stably finite and `Cu(A)` is algebraic (every element a
supremum of an increasing sequence of compact elements — automatic
under RR0 by Perera), must `A` have real rank zero?

Known: yes under stable rank one (Coward--Elliott--Ivanescu, Cor 5);
false without simplicity in the purely infinite case (Thiel's
`O_∞`-stable extension with an exponential-map obstruction), so any
counterexample mechanism must be `K_1`-free at the ideal level or
simple.

## Attempts

* The open region is higher stable rank, i.e. Villadsen territory once
  more: for a type II Villadsen algebra (unique trace `τ`, stable rank
  `> 1`), `Cu = V(A) ⊔ LAff` is algebraic iff `ρ(K_0)` is dense in the
  reals below each soft level — a countable-density computation in the
  same seed combinatorics as the XXVII no-gos.  If some V2 variant has
  dense pairing image (algebraic Cu) while higher stable rank blocks
  the CEI projection-lifting argument, XXXI is refuted; if Euler
  rigidity always sparsifies `ρ(K_0)` in the non-sr1 regime, the
  problem survives exactly on the sr1 boundary where CEI already
  proves it.  Either way the deciding quantity is the density of the
  trace-pairing image under coordinate-duplicating branch maps —
  computable per system, unresolved in general.
* Note the asymmetry with Problem XXX: there RR0 is the hypothesis,
  here it is the goal; a positive XXXI plus algebraic-Cu-preserving
  regularization would transfer XXX-type questions to the Cuntz
  semigroup, where the XXVI/XXVII machinery applies.
