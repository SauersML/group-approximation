---
rg: 2
id: rational-germ-singular-sets-are-finite-graph-path-spaces
kind: claim
title: The singular set of a rational homeomorphism over a boundary Thompson group is the path space of an explicit finite graph, so it is either finite with all points eventually periodic, or contains a Cantor set
distinct_from:
  z2-free-z-normal-form-boundary-has-corner-singular-orbits: that computes the singular set of the Z^2 generators on one normal-form boundary by hand; this computes every singular set of every rational homeomorphism of every normal-form boundary as the path space of a finite graph, and gives the finite-or-Cantor dichotomy that explains both that computation and the F_2 x F_2 failure.
  automatic-groups-embed-in-corner-germ-extensions: that is the OPEN premise (E1)-(E5) for all automatic groups; this makes its condition (E1) a decidable property of a transducer rather than an existential statement.
  finite-state-mobius-pieces-see-finitely-many-primes: that bounds which primes appear in the affine pieces of a finite-state automorphism of a p-adic tree; this is about which points fail to be locally prefix replacements, with no arithmetic content.
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

**ESTABLISHED** by `rational-germ-singular-sets-graph-path-space-proof` (lane proof,
elementary, not independently reviewed; no priority claimed).

## Setting

Let `X` be a finite alphabet and `L ⊆ X^*` a regular language of normal forms for a group `G`
in the sense of Belk--Bleak--Chatterji--Matucci--Perego (BBCMP), *Rational embeddings of
continuous automatic groups* (preliminary version 2026; read at source, pp. 2--6). Let
`∂L ⊆ X^ω` be its boundary, a closed rational set (BBCMP p. 5), and assume `∂L` has no
isolated points.

- For a word `u` that is a prefix of a point of `∂L` write `[u] = {ξ ∈ ∂L : u < ξ}` and
  `Fol(u) = {η ∈ X^ω : uη ∈ ∂L}`. Regularity of `L` gives finitely many sets `Fol(u)`.
- `B`, the **boundary Thompson group** of `L`, is the group of all `h ∈ Homeo(∂L)` such that
  every `ξ ∈ ∂L` has prefixes `u < ξ` and `u' < h(ξ)` with `Fol(u) = Fol(u')` and
  `h(uη) = u'η` for all `η ∈ Fol(u)`. A map of that last form is a **prefix replacement**.
  `B` is a group and is full by construction.
- `sing_B(h) = {ξ ∈ ∂L : h agrees with no element of B on any neighbourhood of ξ}`, as in
  Belk--Hyde--Matucci (BHM) arXiv:2407.03149 §1.
- `h ∈ Homeo(∂L)` is **rational** if some finite-state asynchronous transducer computes it
  (Grigorchuk--Nekrashevych--Suschanskii); equivalently (BBCMP Thm 1.7) its graph is a
  deterministic rational subset of `X^ω × X^ω`. By BBCMP Cor 1.8 every continuous asynchronous
  automatic group acts on `∂L` by rational homeomorphisms.
- Fix a transducer for `h`. For a prefix `u` let `out(u)` be the word emitted while reading `u`
  and let the **section** `h_u` be the map with `h(uη) = out(u)·h_u(η)` for `η ∈ Fol(u)`.
  Rationality says the set of sections is finite.
- Call the triple `(h_u, Fol(u), Fol(out(u)))` **regular** if `h_u` is a prefix-prepending map,
  `h_u(η) = e·η` for a fixed word `e` and all `η ∈ Fol(u)`, with `Fol(u) = Fol(out(u)·e)`.
  Regularity depends only on the triple, and there are finitely many triples.

## Statement

Let `h` be a rational homeomorphism of `∂L`.

1. **Pointwise criterion.** `ξ ∉ sing_B(h)` if and only if the triple at `ξ_1 … ξ_n` is regular
   for some `n ≥ 0`. (A regular triple exhibits `h` as one prefix replacement on `[ξ_1 … ξ_n]`;
   conversely a prefix replacement near `ξ` forces regularity at infinitely many `n`.)
2. **Graph description.** Let `Λ_h` be the finite directed graph whose vertices are the
   non-regular triples `(q, F, F')` reachable by reading prefixes of points of `∂L`, with an
   edge `(q,F,F') --x--> (q·x, F·x, F'·λ(q,x))` whenever `x` is legal at `F` and the target is
   non-regular. Then `sing_B(h)` is the set of infinite paths of `Λ_h` from the start vertex,
   read as letters. In particular `sing_B(h)` is a closed rational subset of `∂L`, computable
   from any transducer for `h`.
3. **Dichotomy.** Prune `Λ_h` to the vertices lying on an infinite forward path. Then
   `sing_B(h)` is finite if and only if every pruned vertex lying on a cycle has out-degree
   one. In that case every point of `sing_B(h)` is eventually periodic: a finite path followed
   by one cycle traversed forever.
4. **Failure is uncountable.** If some pruned vertex on a cycle has two distinct return paths
   to itself, equivalently its strongly connected component is not a single cycle, then
   `sing_B(h)` contains a Cantor set.
5. **Decidability.** Given a transducer for `h` and an automaton for `∂L`, the condition in
   item 3 is decidable and the finitely many singular points are computable.

Call `h` **thin** when item 3 holds.

## Why it matters

- Condition (E1) of `automatic-groups-embed-in-corner-germ-extensions` asks that every element
  of the host have finitely many singular points. Items 3 and 5 turn that into a finite check
  on the word-difference data of the generators, for any given continuous asynchronous
  automatic structure, and item 4 says the check has no middle ground.
- Item 3 forces every singular point to be eventually periodic, which is what makes the germ
  condition (E4) concrete; see `germ-rate-homomorphism-tests-germ-extension-finiteness`.

## Calibration

- **Z^2 * Z.** `z2-free-z-normal-form-boundary-has-corner-singular-orbits` computes
  `sing(x^±) = sing(y^±) = ` the four corners `(x^ε y^δ)^∞`. There `Λ_x` is four disjoint
  loops: four cycle vertices of out-degree one, giving four eventually periodic singular
  points, as item 3 predicts.
- **F_2 × F_2 with the product normal form.** For a second-factor generator the sections stay
  non-regular along every first-factor word, so the pruned graph contains the whole
  first-factor boundary graph, whose strongly connected component has two distinct return
  paths. Item 4 gives a Cantor set of singular points, which is the failure recorded in
  `automatic-groups-embed-in-corner-germ-extensions`.

## Scope

- Rationality is a hypothesis. For continuous asynchronous automatic structures it is BBCMP
  Cor 1.8, read at source; nothing here reproves it.
- Items 3 and 5 are effective only relative to a given transducer. Nothing here produces a
  transducer, or decides whether a given group has some thin structure.
- Nothing here addresses (E2), (E3) or (E5).
