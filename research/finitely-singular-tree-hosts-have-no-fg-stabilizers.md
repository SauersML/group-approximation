---
rg: 2
id: finitely-singular-tree-hosts-have-no-fg-stabilizers
kind: claim
title: A micro-supported tree action by automorphisms with finitely many singular vertices over a subgroup with trivial edge stabilizers has no finitely generated vertex, edge or half-tree stabilizer, in any valence, so finitary local-rule Tits-(P) hosts cannot have finitely generated edge groups
distinct_from:
  micro-supported-tree-actions-self-embed-rigid-stabilizers: that proves every rigid stabilizer of a micro-supported tree action contains an infinite direct sum of copies of itself; this adds a singular-depth filtration on stabilizers, valid when all elements are finitely singular over an edge-free core, and deduces that no stabilizer is finitely generated.
  tits-independence-vertex-groups-are-branch-type: that uses local finiteness and (P) to make vertex stabilizers branch-type groups; this needs neither, works in infinite valence, and kills finite generation of stabilizers for the finitary class instead.
  fg-simple-hyperlinear-tree-group-not-finitely-presented: that imports Le Boudec's groups G(F,F') and their locally finite vertex stabilizers as a calibration; this is a general theorem whose special case (core U(F), F semiregular) recovers the non-finite-generation of those stabilizers, on trees of any valence and for every edge-free core.
  tits-independence-amalgams-force-self-product-edge-groups: that finds V x V inside the edge factor of a (P)-amalgam; this shows that when the host is finitary over an edge-free core the edge group is not even finitely generated.
---

**ESTABLISHED (unreviewed).** Proof: `finitely-singular-tree-hosts-no-fg-stabilizers-proof`.

**Setting.** `T` is a tree of any valence. `G ≤ Aut(T)` is **edge-free**: the only
element of `G` fixing two adjacent vertices is `1`. Fix an integer `ρ ≥ 1`. For
`g ∈ Aut(T)`, a vertex `v` is **regular** for `g` if some `h ∈ G` agrees with `g`
on the ball `B_ρ(v)`; otherwise `v` is **singular**. Put `Sing(g)` for the set of
singular vertices and

`Γ(G, ρ) = {g ∈ Aut(T) : Sing(g) is finite}`.

For a half-tree `Y`, `R_Γ(Y)` is the rigid stabilizer: elements of `Γ` fixing every
vertex outside `Y`.

**Theorem.**

1. **The finitary host is a group.** `Sing(gh) ⊆ Sing(h) ∪ h^{-1} Sing(g)` and
   `Sing(g^{-1}) = g Sing(g)`. So `Γ(G, ρ)` is a subgroup of `Aut(T)` containing
   `G`. For `ρ = 1` it has Tits' property (P), in every valence.
2. **Rigidity.** If `1 ≠ r ∈ Aut(T)` fixes every vertex outside a half-tree `Y`,
   then `Sing(r) ∩ Y ≠ ∅`.
3. **Singular-depth filtration.** Let `Γ ≤ Γ(G, ρ)` and let `σ` be a vertex or an
   edge of `T`, with `d_σ` the distance to `σ`. On the stabilizer `Γ_σ` (fixing
   the endpoints, if `σ` is an edge), the singular depth
   `D(g) = max{d_σ(u) : u ∈ Sing(g)}` satisfies `D(gh) ≤ max(D(g), D(h))` and
   `D(g^{-1}) = D(g)`. So `Γ_σ` is the increasing union of the subgroups
   `Γ_σ^{(k)} = {D ≤ k}`. Every finitely generated `H ≤ Γ_σ` lies in some
   `Γ_σ^{(k)}`, and then `H ∩ R_Γ(Y) = 1` for every half-tree `Y` all of whose
   vertices are at distance `> k` from `σ`.
4. **No finitely generated stabilizers.** Let `Γ ≤ Γ(G, ρ)` act minimally, with
   no fixed end, on a tree that is not a line, with `R_Γ(Y_0) ≠ 1` for some
   half-tree `Y_0`. Then no vertex stabilizer `Γ_v`, no edge stabilizer `Γ_f` and
   no rigid stabilizer `R_Γ(Y)` is finitely generated. Every finitely generated
   subgroup of `Γ_v` meets all sufficiently deep rigid stabilizers trivially.
5. **Kill for the Tits route.** A group `Γ` acting faithfully, minimally, without
   fixed end, on a tree that is not a line, with (P) and a nontrivial finitely
   generated edge stabilizer, is contained in `Γ(G, ρ)` for **no** edge-free
   `G ≤ Aut(T)` and **no** `ρ`. Equivalently, for every such `G` and `ρ` some
   element of `Γ` has infinitely many singular vertices.

**What it kills.**

- **Finitary local-rule hosts.** Take a legal colouring of `T_d` and a semiregular
  `F ≤ Sym(d)`, so that `U(F)` is edge-free. Le Boudec's `G(F, F')` (local action
  in `F'` everywhere and in `F` off a finite set) lies in `Γ(U(F), 1)`. Item 4
  reproves that its stabilizers are not finitely generated, without using local
  finiteness of stabilizers.
- **The same construction in infinite valence.** Colour the edges at each vertex
  of the countable-valence tree by a countable set `S`, fix a group `F` acting
  freely on `S` and any `F' ≤ Sym(S)` containing `F`. The groups of automorphisms
  with local action in `F'` everywhere and in `F` off finitely many vertices have
  (P). Whenever they act minimally without fixed end and some edge group is
  nontrivial, no edge group is finitely generated.
- **(P)-closures of free products.** For a free product (more generally any
  fundamental group of a graph of groups with trivial edge groups) acting on its
  Bass--Serre tree, of any valence, the finitary gluing closure `Γ(G, 1)` has (P).
  By item 5, no subgroup of it that acts minimally without fixed end, not on a
  line, with (P), has a nontrivial finitely generated edge group.

The failing step is item 3: products of elements fixing `σ` never push
singularities outward, and item 2 forces every nontrivial element of a deep rigid
stabilizer to have a deep singularity.

**What survives.** For `boone-higman-conjecture`, a Tits-(P) host with a finitely
generated edge group, as asked in Attempt 8, must contain elements with infinitely
many singular vertices over every edge-free core. These are automaton-type or
branch-type tree automorphisms, as in the locally finite case
(`tits-independence-vertex-groups-are-branch-type`). The live question becomes
whether such infinitely singular (P)-groups of infinite valence can be finitely
presented.

**Calibration.**

- **`Aut(T_d)`, `d ≥ 3`.** It has (P), (M), (N) and uncountable stabilizers.
  Consistently, it contains elements with infinitely many singular vertices over
  every countable edge-free `G`.
- **A free product `A * B` of finite groups** is edge-free, so it lies in
  `Γ(A * B, 1)` with no singular vertices. All its rigid stabilizers are trivial,
  so item 4 does not apply, and its stabilizers are finite.
- **Le Boudec's groups** are finitely generated while their stabilizers are not,
  as item 4 predicts. The theorem says nothing about finite generation of `Γ`
  itself.
