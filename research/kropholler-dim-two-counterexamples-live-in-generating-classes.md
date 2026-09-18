---
rg: 2
id: kropholler-dim-two-counterexamples-live-in-generating-classes
kind: claim
title: Extensions and directed unions cannot create a two-dimensional counterexample to Kropholler's question; any counterexample in the extension-union closure of a subgroup-closed amenable class X contains a finitely generated counterexample lying in X
distinct_from:
  amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical: that excludes one extension step with an elementary amenable kernel for a finitely generated group; this iterates the step transfinitely through an arbitrary extension-union hierarchy over an arbitrary base class, where kernels and quotients are not elementary amenable and quotients have no cd bound
  amenable-cd-two-kropholler-iff-locally-indicable: that reduces the question to finitely generated groups with finite abelianization; this reduces it, inside any generating class, to the base class of that class
  hillman-linnell-finite-hirsch-length-theorem: that is the elementary amenable case; the base case X = {finite and abelian groups} of this statement returns only elementary amenability itself and no classification
---

**ESTABLISHED** (proposed; referee pending) through
`kropholler-dim-two-generating-class-descent-proof`, from
`amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical` (item 2) and Stallings–Swan.

A *two-dimensional counterexample* is an amenable group of `cd_Z <= 2` that is not elementary
amenable (EA). Let `X` be a class of amenable groups closed under subgroups and isomorphism.
Let `ED(X)` be the smallest class containing `X` and closed under extensions and directed
unions. Equivalently `ED(X) = ∪_α L_α`, where `L_0 = X`, `L_{α+1}` consists of the directed
unions of groups `H` having a normal subgroup `N` with `N` and `H/N` in `L_α`, and
`L_λ = ∪_{α<λ} L_α` at limits. Then:

1. **Hierarchy.** Every `L_α`, and `ED(X)`, is closed under subgroups. If `X` is also closed
   under quotients, so is every `L_α` and `ED(X)`. So `ED(X)` is the smallest class containing
   `X` closed under subgroups, extensions and directed unions (and quotients, if `X` is).
2. **Descent.** Let `G ∈ ED(X)` with `cd_Z G <= 2`. If every subgroup of `G` that lies in `X`
   is EA, then `G` is EA.
3. **Consequence.** Every two-dimensional counterexample `G ∈ ED(X)` contains a finitely
   generated two-dimensional counterexample `H ≤ G` with `H ∈ X`. In particular, if no group of
   `X` is a two-dimensional counterexample, none of `ED(X)` is.

**What it kills.** Every construction of a two-dimensional counterexample that builds the group
by extensions and directed unions from simpler amenable pieces. The counterexample must already
be present, as a finitely generated subgroup, among the pieces. Iterated extensions cannot
help, even though the kernels and quotients at each step need not have finite cohomological
dimension (the quotient `H/N` of a cd-2 group can have infinite cd), and even when the pieces
themselves are not EA. The exact point where each step is absorbed is item 2 of
`amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`. A finitely generated subgroup `F`
either meets the kernel, and then it has a nontrivial EA normal subgroup and is `BS(1,m)`, or it
embeds in the quotient, and then it lies one level lower.

**Instances.**

- `X` = finite and abelian groups gives `ED(X)` = EA. The statement is then empty.
- `X` = groups all of whose finitely generated subgroups have subexponential growth gives
  Grigorchuk's class `SG` of subexponentially amenable groups. See
  `subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth`. Every counterexample in `SG`
  contains a finitely generated group of intermediate growth of cd 2.
- `X` = amenable groups without free subsemigroups of rank two (closed under subgroups and
  quotients). Its closure contains `SG`.
- `X` = all amenable groups gives nothing. So the statement matters only for a generating class
  smaller than all amenable groups.

**Why dimension 2.** The only non-formal input is "a finitely generated amenable group of
cd 2 with a nontrivial EA normal subgroup is EA". In dimension `n`, the same argument proves the
analogous descent from exactly the analogous input for cd `n`, which is not known.
