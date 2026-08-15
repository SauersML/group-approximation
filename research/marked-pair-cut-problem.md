---
rg: 2
id: marked-pair-cut-problem
kind: claim
title: An ε-deletion cuts every kernel-transporter walk in deep congruence models
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
- **If refuted:** only the exact-congruence lane closes; the two-point
  claim survives on other models.  But the refutation would be an
  expansion argument, and by the approximate-model remark of
  `pair-constraint-graph-criterion` an expansion argument robust to `k`
  single-letter Hamming defects refutes `two-point-orbit-approximation`
  outright — and with it, through
  `witness-yields-two-point-approximation`, the witness claim itself,
  resolving the Hilbert-embeddable lane negatively.  A refutation attempt
  should therefore be run at approximate-model strength from the start.

The regular congruence model is the canonical test case, not the general
one: `two-point-orbit-approximation` admits arbitrary finite models, and
non-free or induced congruence actions are legitimate variants if the
regular one fails for removable reasons.
