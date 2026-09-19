---
rg: 2
id: kazhdan-host-crossed-product-is-simple-and-nuclear
kind: claim
title: "The amenable Kazhdan host's crossed product C(M) x|_r Gamma is unital, separable, simple and nuclear, with verbatim sources, for the M actually built by the host route"
distinct_from:
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that builds the host and asserts freeness, minimality, topological amenability and pure infiniteness of the groupoid; this is the C*-level consequence for its specific M, namely simplicity and nuclearity of the reduced crossed product, which the host node does not derive and which the Rordam-Sierakowski existence statement does not supply.
  nv-brick-groupoid-and-kazhdan-host-are-both-o2: that is the O_2 computation for all three groupoids; this is the single import gap its Step 5 needs, isolated so that the computation derives once the gap is filled.
  trivial-k-theory-kirchberg-algebras-are-o2: that is the UCT-equivalent classification question; this asks only for two standard permanence theorems about reduced crossed products, with no classification content.
artifacts: []
---

**Status: OPEN.** This is a referee gap, opened 2026-09-18, not a new research
direction: what it asks for is two standard theorems quoted verbatim against their
sources.

## Statement

Let `M` be the Cantor set and `Γ = Z^3 ⋊ SL_3(Z) ↷ M` the action constructed in
Steps 1–3 of `amenable-purely-infinite-groupoid-kazhdan-host-proof` (a Zorn-minimal
closed invariant subset of `X' × Z` with `X' ⊆ T^Γ`), i.e. the action underlying the host
`𝒢_W1 = (M ⋊ Γ) × G_2` of
`amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`. Then

`A := C(M) ⋊_r Γ`

is unital, separable, **simple** and **nuclear**.

## Why it is open, and what would close it

`nv-brick-groupoid-and-kazhdan-host-are-both-o2-proof` Step 5 obtained exactly these four
properties by quoting Rørdam–Sierakowski (arXiv:1006.1304v3, l.1443–1449):

> "Let `G` be a countable discrete group. Then `G` admits a free, amenable, minimal
> action on the Cantor set `X` such that `C(X) ⋊_r G` is a Kirchberg algebra […] in the
> UCT class if and only if `G` is exact and non-amenable."

That is an **existence** statement — it produces *some* action of `Γ` — and the host's `M`
is not that action; it is built independently, and the host node cites Rørdam–Sierakowski
only under "Prior art and novelty", noting that "Steps 1–3 of the route reprove the free,
amenable, minimal part". So the quoted sentence says nothing about this `A`.

The properties are expected to be true for this `M`, but via two theorems that appear
nowhere in the route's `requires:` list or text:

- **(N)** a topologically amenable action of a discrete group on a compact space has
  nuclear reduced crossed product (Anantharaman-Delaroche);
- **(S)** a topologically free minimal action has simple reduced crossed product
  (Archbold–Spielberg).

Closing this claim means recording (N) and (S) as literature imports with verbatim
sources in the repository convention, and checking that the host's action satisfies their
hypotheses (free ⇒ topologically free; minimal and topologically amenable are asserted by
the host node). Nothing beyond that is needed: pure infiniteness and the UCT are not used
downstream.

A secondary hypothesis mismatch flagged in the same referee pass, which this claim also
absorbs: the Rørdam–Sierakowski sentence needs `Γ` **exact**, while Step 5 supplied
property A (`commutative-ring-linear-groups-have-property-a`), and Ozawa's
property A ⟺ exactness for discrete groups is cited nowhere on the graph. Under (N) and
(S) the exactness route is not needed at all, which is the cheaper repair.

## Attempts

- **2026-09-18 (referee pass on the landing of
  `nv-brick-groupoid-and-kazhdan-host-are-both-o2`).** Referee lens 2 refuted the O_2
  computation at exactly this point, calling it a quantifier inversion on the load-bearing
  import: the Rørdam–Sierakowski statement is existential and was applied universally to
  the host's specific `M`. The lens confirmed that the four properties themselves are
  true for this `M`, and named (N) and (S) as the fix. **Where it stops:** neither (N) nor
  (S) is on the graph, so the implication cannot be compiled yet. Lens 1 and lens 3 both
  read Step 5 as sound, lens 3 explicitly accepting the Rørdam–Sierakowski appeal, so the
  gap is a single-lens finding — but an unrebutted one.
