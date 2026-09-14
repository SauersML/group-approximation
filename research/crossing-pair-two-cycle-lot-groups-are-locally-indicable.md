---
rg: 2
id: crossing-pair-two-cycle-lot-groups-are-locally-indicable
kind: claim
title: A reduced LOT whose left graph has cyclomatic number two and a separated crossing pair has a locally indicable, torsion-free group and an aspherical complex
distinct_from:
  lot-groups-are-torsion-free: that is the open statement for every LOT group; this proves local indicability, hence torsion-freeness, for an infinite class not covered by the one-cycle criterion.
  barreto-minian-concatenable-minima-give-local-indicability: that is the presentation criterion; this is the LOT class on which it holds after one Tietze elimination, with the minima computed exactly.
  lot-complexes-with-at-most-seven-vertices-are-aspherical: that is a finite census on at most seven vertices; this is an infinite class with no bound on the number of vertices.
  injective-labeled-oriented-trees-are-aspherical: that covers LOTs in which each vertex labels at most one edge; this imposes a condition on the left graph instead.
  reduced-lots-have-concatenable-tietze-presentations: that is the open statement that every reduced LOT has a minima-concatenable Tietze presentation; this proves it for one class with an explicit one-step elimination.
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
  - experiments/lot-torsion/crossing_pair_check.py
  - experiments/lot-torsion/crossing_pair_check-run.log
---

**ESTABLISHED** through `crossing-pair-two-cycle-lot-li-proof`. Unreviewed. No novelty is claimed;
Howie 1985 was not read.

**Conventions.** A LOT `Γ` has edges `e = (i(e), λ(e), t(e))` and relators
`r_e = i(e) λ(e) t(e)^-1 λ(e)^-1`. It is *compressed* if `λ(e) ∉ {i(e), t(e)}` for every `e`, and
*interior reduced* if no vertex has two incident edges with the same label that both point away
from it or both point towards it. The **left graph** `T(Γ)` is the multigraph on the vertices with
one edge `{i(e), λ(e)}` for each edge `e`. Its *cyclomatic number* is `#edges - #vertices +
#components`.

A **crossing pair** is a pair of edges `e = (v, u, t_e)` and `f = (u, v, t_f)`, so
`i(e) = λ(f) = v` and `λ(e) = i(f) = u`. They give two parallel left edges `{u, v}`.

**Claim.** Let `Γ` be a compressed, interior reduced LOT such that `T(Γ)` has cyclomatic number
`2` and contains a crossing pair `e = (v, u, t_e)`, `f = (u, v, t_f)` with `t_e ≠ t_f`.
- Let `T_1` be the multigraph obtained from `T(Γ)` by deleting the left edges of `e` and `f` and
  identifying `v` with `u`. It has cyclomatic number `1`.
- Suppose some edge `s` of the cycle of `T_1` leaves a forest `F = T_1 - s` in which the component
  of `t_e` contains neither `u` nor `t_f`, or the component of `t_f` contains neither `u` nor
  `t_e`.

Then:
1. eliminating the generator `v` with the relator of `e` gives a presentation of `G(Γ)` satisfying
   `barreto-minian-concatenable-minima-give-local-indicability` with the relator of `s` omitted;
2. `G(Γ)` is locally indicable, and in particular torsion-free;
3. `K(Γ)` is aspherical.

**Mirror form.** Reversing every edge, `(i, λ, t) ↦ (t, λ, i)`, gives a LOT with an isomorphic group
(substitute `x ↦ x^-1`), and its left graph is the **right graph** `I(Γ)` (edges `{λ(e), t(e)}`). So
the same statement holds with `I(Γ)` and crossing pairs `(t_e, u, v)`, `(t_f, v, u)`.

**Relation to known criteria.** Barreto--Minian's Corollary 3.1 needs `T(Γ)` or `I(Γ)` to have at
most one cycle. Here `T(Γ)` has two independent cycles; the class adds content exactly when `I(Γ)`
also has at least two.

**Model test** (`experiments/lot-torsion/crossing_pair_check.py`, log in the artifact list), using
the census code on main:
- 16902 (crossing pair, omitted relator) instances from 4409 random reduced LOTs on 8--10 vertices
  and the 13 hardest seven-vertex classes;
- predicted minima equal computed minima every time;
- predicted and computed concatenability agree every time, including every failing instance;
- every predicted pass also passes the census tester for Theorem 2.5.

**Coverage.**
- 12 of the 13 seven-vertex classes that the census could certify only after Tietze closure satisfy
  the claim on one side.
- Among the sampled reduced LOTs on 8--10 vertices where neither graph has at most one cycle, 65 of
  124 satisfy it.
