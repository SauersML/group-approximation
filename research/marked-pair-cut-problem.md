---
rg: 2
id: marked-pair-cut-problem
kind: claim
title: An ε-deletion cuts every kernel-transporter walk in deep congruence models
refuted_by: exact-models-cannot-separate-marked-pair
distinct_from:
  two-point-orbit-approximation: that quantifies over all approximately multiplicative models; this fixes the exact regular congruence model and asks for the deleted set there — a strictly stronger statement that can fail by expansion while that claim survives on other models.
  congruence-transporter-girth: that proves the absence of short kernel-transporter words in deep congruence quotients; this asks to cut the walks of the long ones, which exist at every level.
  hs-expander-block-decomposition: that seeks a normalized-HS analogue of Kun's expander decomposition for approximate representations; this is a set-level vertex-deletion problem on a congruence Schreier graph, with no Hilbert space in it.
---

Let everything be as in `congruence-transporter-girth`: the Theorem E pair,
the marked pair `(p,q) = (Γ, hΓ)`, the congruence quotients `π_M`, the
regular models `A = Q_M` with `φ_M` = left translation through `π_M`, and
the pair-constraint graph `𝒢(Q_M, φ_M, F)` of
`pair-constraint-graph-criterion`.

**The claim.**  For every finite `F ⊆ G` and `ε > 0` there exists `M` and
`S ⊆ Q_M` with `|S| > (1-ε)|Q_M|` such that for every `s ∈ S` the vertices
`(s,p)` and `(s,q)` lie in **distinct components** of `𝒢(Q_M, φ_M, F)`
restricted to `S × {p,q}`.

By item 1 of `pair-constraint-graph-criterion` this is exactly two-point
label data on the exact congruence model, so this claim routes directly
into `two-point-orbit-approximation` (route
`two-point-via-congruence-cuts`).

## REFUTED (2026-08-15)

This claim is **false**, and in the stronger form covering every exact
model, not only the regular congruence ones:
`exact-models-cannot-separate-marked-pair` (established, with proof) shows
that for the window `F₀ = S_Γ ∪ S_Γ^{-1} ∪ {h}` and any
`ε < ε₀(κ, |S_Γ|)`, no genuine finite `G`-action admits a deleted set of
density `ε` separating the marked pair.  The mechanism: exactness forces
`φ(h) ∈ φ(Γ)`, the `h`-matching then preserves every `Γ`-orbit, and
property (T) makes the `p`-slot Schreier sheet an expander that an
ε-density deletion cannot fragment — expansion beats girth.  The route
`two-point-via-congruence-cuts` is invalidated by that claim.  No route
should ever require this claim; it is retained as the record of the
question and of the attack log below.

## The shape of the problem

With `S = Q_M` the claim is false at every level: `ker π_M ∩ hΓ` is
nonempty (`congruence-transporter-girth` item 1), any such `v` spells a
slot-admissible `F'`-word for a large enough window `F' ⊇ F`, and its
traversal is a closed walk joining `(s,p)` to `(s,q)` based at **every**
`s`.  So the deleted set has real work to do: it must meet the walk of
every kernel transporter at almost every basepoint, using only `ε|Q_M|`
deletions.  What the girth theorem contributes is that every such walk is
long — length `≥ log_{C(F)}(M/2) − 1` — so the deletions can be spent at
density `≈ 1/girth` per walk rather than per edge.  The problem is a race
between the window's budget `1/ε` and congruence depth `M`, with the girth
guaranteeing the budget is never violated by any single walk.

## Why it may be false, and what each outcome pays

`G` has Kazhdan's property (T), so the Schreier graphs of the congruence
models form expander families, and the bad walks are not arbitrary: they
realize a fixed nontrivial class (the image of the transporter coset `hΓ`)
at every basepoint.  Cutting every representative of a fixed class at
almost every basepoint with a sublinear vertex deletion is exactly the kind
of statement expansion refutes — this is the Kun--Thom mechanism one level
below soficity, and a frustration-index lower bound uniform in `M` would
refute this claim.

- **If proved:** `two-point-orbit-approximation` becomes established via
  the recorded route, and the cheapest refutation surface of the
  Hilbert-embeddable witness lane closes — refuting
  `hilbert-embeddable-witness-for-kun-thom-wreath` would then need tools
  finer than the two-point necessary condition.
- **If refuted:** only the exact-model lane closes; the two-point claim
  survives on genuinely approximate models.  *Correction (2026-08-15,
  from the adversarial verification of the actual refutation):* the
  earlier version of this bullet asserted that any expansion refutation
  would automatically be robust to Hamming defects and so refute
  `two-point-orbit-approximation` outright.  That was wrong.  The
  refutation's load-bearing input is `φ(h) ∈ φ(Γ)` — a strictly
  exact-model fact with no Hamming-robust analogue: an
  `(F,ε)`-multiplicative `φ` need not place `φ(h)` near any `φ(γ)`, and
  the orbit decomposition is then undefined.  Extending to approximate
  models is a genuinely open problem, not a corollary.

The regular congruence model is the canonical test case, not the general
one: `two-point-orbit-approximation` admits arbitrary finite models, and
non-free or induced congruence actions are legitimate variants if the
regular one fails for removable reasons.
