---
rg: 2
id: cantor-punctured-birman-sections-have-no-finite-end-orbit
kind: claim
title: A section of the forgetful map from a closed surface's mapping class group relative to a closed totally disconnected set has no finite orbit on that set
distinct_from:
  birman-exact-sequence-does-not-virtually-split: that is the one-point case, sections into the mapping class group of a once-marked surface; this is its consequence for an arbitrary closed totally disconnected marked set, such as a Cantor set, where a finite orbit would produce a one-point section over a finite-index subgroup.
  closed-mcgs-have-no-covering-lift-to-marked-covers: that excludes lifts to finite covers with finitely many marked points; this concerns the same surface marked along an infinite set, where sections are not excluded but are forced to move every marked point infinitely often.
artifacts:
  - research/artifacts/bh-mcg-closed-surface-2026-09-12.md
---

**ESTABLISHED.** Let `Σ` be a closed orientable surface of genus `g ≥ 3` and
`E ⊂ Σ` a nonempty closed totally disconnected subset (finite, or a Cantor set).

- `Mod(Σ, E)` is the group of orientation-preserving homeomorphisms `h` of `Σ`
  with `h(E) = E`, modulo isotopy through such homeomorphisms.
- `F: Mod(Σ, E) → Mod(Σ)` forgets `E`.

Let `L ≤ Mod(Σ)` have finite index and let `σ: L → Mod(Σ, E)` be a homomorphism
with `F∘σ = id_L`. `σ` need not be injective. Then every orbit of `σ(L)` on `E`
is infinite.

`Mod(Σ, E)` acts on `E`: an isotopy through homeomorphisms preserving `E` moves
each point of `E` along a path in `E`, which is constant because `E` is totally
disconnected.

**Why it matters.** Closed surfaces punctured along a Cantor set are where the
asymptotic mapping class groups of Aramayona--Funar (arXiv:1701.08132) live.
These are candidate finitely presented hosts for `Mod(Σ)`. The natural way to
place `Mod(Σ)` in a group of mapping classes of `(Σ, E)` is a section of the
forgetful map. This claim says any such section, even over a finite-index
subgroup and even non-injective, moves every point of the Cantor set through an
infinite orbit. So its action on `E` has no finite orbit, even virtually.

**Scope.**
- **Sections of the forgetful map only.** Abstract embeddings of `L` into
  `Mod(Σ, E)` that do not lift the identity are not constrained here.
- **Finite `E`.** Every orbit is finite, so no such `σ` exists. This recovers
  non-splitting over finite-index subgroups for any finite marked set.
- **Identification with `Map(Σ ∖ E)`.** Hosts are often defined inside the
  mapping class group of the open surface `Σ ∖ E`. Their comparison with
  `Mod(Σ, E)`, through extension of homeomorphisms to the end compactification,
  is standard and is not re-proved here.
- **Genus 3** rests on `birman-sequence-genus-three-does-not-virtually-split`.

The derivation is `cantor-punctured-birman-section-orbit-proof`.
