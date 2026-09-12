---
rg: 2
id: klyachko-kl-holds-for-torsion-free
kind: claim
title: Klyachko's torsion-free theorem, and the slice of the falsification instrument it removes
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that derives the conjecture from an approximation property, Connes embeddability, which is what makes it usable as a falsification test for hyperlinearity; this derives the unimodular case from torsion-freeness alone, with no approximation input, and its effect on the graph is to narrow the test rather than to supply one.
  kl-violating-equation-over-leavitt-unit-group: that asks for a violation over one specific group, which has torsion; this is a positive theorem about torsion-free coefficient groups and leaves that target untouched.
  hnn-torsion-theorem: that is a permanence lemma saying an HNN extension of a torsion-free base stays torsion-free, a step in building torsion-free examples; this takes torsion-freeness as given and draws an equation-solving conclusion from it.
  torsion-free-higman-embedding: that embeds a recursively presented torsion-free group into a finitely presented torsion-free one; this says nothing about presentations and concerns which one-variable equations are solvable over a torsion-free coefficient group.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

A. A. Klyachko, *A funny property of a sphere and equations over groups*,
Comm. Algebra 21 (1993), 2555--2575: every **unimodular** equation over a
torsion-free group is solvable over it.  Equivalently, for `G` torsion-free
and `w in G * <t>` with `deg_t(w) = ±1`, the coefficient map
`G -> (G * <t>)/<<w>>` is injective.  No approximation property of `G` is
used, and the exponent-sum restriction is essential to the statement.

## What it removes, and what it leaves

The graph carries a falsification instrument: Kervaire--Laudenbach holds for
every hyperlinear group (`kervaire-laudenbach-holds-for-hyperlinear`), so a
nonsingular equation with no solution in any overgroup proves its coefficient
group nonhyperlinear — `kl-violating-equation-over-leavitt-unit-group`,
`kl-violation-refutes-hyperlinearity-route`.

Over a **torsion-free** coefficient group, Klyachko removes the `|m| = 1`
slice of that instrument outright: no unimodular violation exists there, for
any torsion-free group, whatever its approximation properties.  It does not
remove the rest.  What
`kervaire-laudenbach-holds-for-hyperlinear` supplies is the *nonsingular*
statement, so a violation at any nonzero degree refutes hyperlinearity; over
a torsion-free candidate the instrument therefore survives at `|m| >= 2` and
only there.  Klyachko's theorem does not cover that range and nothing in this
graph does.  (The parallel Kervaire--Laudenbach ingestion of the same day
records the same degree asymmetry from the other side, in
`weak-kervaire-transfers-only-at-unimodular-degree`: the scope caution binds
proofs coming in, not counterexamples going out.)

So the honest reading is a search restriction, not a closure: a future
torsion-free nonsofic or nonhyperlinear candidate arrives with the unimodular
half of this route already dead, and any write-up claiming a unimodular
violation over a torsion-free group is wrong before it is read.

## It costs the existing route nothing

`R^x = L_(F_2)(1,2)^x` contains a copy of Thompson's group `V`
(`leavitt-cylinder-swaps-generate-thompson-in-el`), and `V` has torsion, so `R^x` is not
torsion-free and Klyachko does not apply to it at any degree.  The Kun--Thom
wreath products contain their `Z/2Z` lamps, so they are not torsion-free
either.

An external audit ingested on 2026-08-17 offered "Kervaire--Laudenbach for
the torsion-free examples" as one of its settled sofic dividends.  Over this
repository's two families that conclusion is vacuous: neither family is
torsion-free, and no torsion-free variant here has established nonsoficity.
The same audit reported this graph as attempting a "weakly sofic implies
Kervaire--Laudenbach" implication; no such implication is asserted anywhere in
this repository — the hypothesis in use is hyperlinearity, with the citation
correction already recorded on `kervaire-laudenbach-holds-for-hyperlinear`.
