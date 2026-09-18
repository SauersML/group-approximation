---
rg: 2
id: kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds
kind: claim
title: Kazhdan inputs of the full-group gate over a fixed scaffold need one-ended uniformly nonamenable Schreier realizations, so amenable, polynomial-growth and virtually free scaffolds are dead while F₂×F₂ passes every test
requires:
  - simple-inputs-in-wobbling-hosts-are-dense-schreier-realizations
  - kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf
  - simple-kazhdan-groups-have-no-proper-co-amenable-subgroups
  - decidable-host-classes-reduce-to-canonical-kazhdan-groups
distinct_from:
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that is the measure-theoretic kill for amenable acting groups, recovered here as item 4 by a direct ℓ² argument. This node adds the kills for virtually free and polynomial-growth scaffolds, and the one-endedness and uniform-nonamenability constraints that hold over every scaffold.
  translation-like-hosts-are-capped-by-separation-profiles: that caps FREE realizations by the input's Cayley graph; this constrains NON-free realizations of Kazhdan inputs, where the Schreier graph replaces the Cayley graph.
---

**ESTABLISHED** (lane proof, bh-gate-u-wobble; elementary except the cited facts; not reviewed; no priority
claimed). Recalled rather than re-read at source:
- Cornulier's characterization of property FW by commensurated subsets;
- the Kazhdan-constant formulation of (T);
- that a quasi-isometry to a tree can be taken with bounded fibres.

## Setting

`G` is infinite, finitely generated, and has property (T), with Kazhdan pair `(S, ε)`. Gate U over a fixed
finitely generated scaffold `Λ` is realized as in `simple-inputs-in-wobbling-hosts-are-dense-schreier-realizations`:
an `R`-realization of `G` on the set `Λ`, with moved set `M` that is `R₀`-dense.

In item 1 below, `M_∞ ⊆ M` denotes the union of the infinite orbits. If `G` is simple, then `M_∞ = M`,
since a finite orbit gives a finite quotient.

## Theorem 2 (necessary conditions)

1. **Uniform nonamenability.** For every finite `A ⊆ M_∞` there is some `s ∈ S` with
   `|A Δ A·s| ≥ ε²|A|`. Every infinite orbit therefore has a Schreier graph with Cheeger constant bounded
   below by a constant depending only on `(S, ε)`, and so has exponential growth.
2. **One-endedness (property FW suffices).** Every infinite orbit has a one-ended Schreier graph.
3. **Growth.** If `M_∞ ≠ ∅`, then `Λ` has exponential growth, so polynomial-growth scaffolds are dead.
4. **Amenable scaffolds are dead.** If `Λ` is amenable, `M_∞` is not `R₀`-dense for any `R₀`. So an
   infinite simple Kazhdan group has no dense realization, and the canonical inputs `H_Γ` never pass gate
   U over an amenable scaffold through the full group.
5. **Virtually free scaffolds are dead.** If `Λ` is virtually free, `M_∞ = ∅`.
6. **Finite orbits over small-separation scaffolds.** If `sep_Λ(n) = o(n)`, the finite orbits of `G` on
   `M` have bounded size. They are uniform expanders by item 1, and expanders have separation `≍ n`. So
   for a residually finite Kazhdan input, faithfulness over such a scaffold must come from infinite
   orbits.

## Proof

**Item 1.** `ℓ²(M_∞)` contains no nonzero `G`-invariant vector, since every orbit in it is infinite. By
(T), for every `ξ` there is `s ∈ S` with `‖sξ − ξ‖ ≥ ε‖ξ‖`. Apply this to `ξ = 1_A`. Cheeger constant
`h > 0` gives `|B(n+1)| ≥ (1 + h)|B(n)|`.

**Item 2.** Suppose an infinite orbit `Ω` had at least two ends. Then some `A ⊆ Ω` with finite edge
boundary would be infinite and co-infinite, so `|A Δ A·s| < ∞` for every `s`, and `A` would be
commensurated. Property FW makes `A` commensurate to a `G`-invariant subset of the transitive set `Ω`,
that is, to `∅` or `Ω`. So `A` would be finite or cofinite, a contradiction.

**Item 3.** The realization is injective on each orbit and `R`-Lipschitz, so `|B_Λ(Rn)| ≥ |B_Ω(n)|`, which
grows exponentially by item 1.

**Item 4.** Let `F ⊂ Λ` be Følner and put `ξ = 1_(F ∩ M_∞)`. Since `M_∞` is invariant and generators move
points at most `R`, `‖sξ − ξ‖² ≤ 2|∂_R F|`. Item 1 then gives `ε²|F ∩ M_∞| ≤ 2|∂_R F|`.

If `M_∞` were `R₀`-dense, every point of `F` at distance more than `R₀` from `Λ ∖ F` would have a point of
`M_∞ ∩ F` within `R₀`. So `|F ∩ M_∞| ≥ (|F| − |∂_(R₀)F|)/|B(R₀)|`. Taking `F` Følner along both
boundaries gives `ε²|F|/|B(R₀)| ≤ o(|F|)`, a contradiction.

The consequence for `H_Γ` follows because `H_Γ` is infinite, simple and Kazhdan
(`decidable-host-classes-reduce-to-canonical-kazhdan-groups`). This agrees with the topological version of
`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`, where every invariant measure on a minimal
subsystem has full support.

**Item 5 (finite-cut pullback).**
- Compose the realization on an infinite orbit `Ω` with a bounded-fibre quasi-isometry `Cay(Λ) → T` to a
  locally finite tree. This gives `f : Ω → T`, Lipschitz with fibres of size at most `C`.
- For an edge `e` of `T`, let `A_e = f⁻¹(one side of e)`. Every Schreier edge crossing `A_e` has an
  endpoint mapped within `R′` of `e`, so `|∂A_e| ≤ C′`, uniformly in `e`.
- `f(Ω)` is infinite, so König's lemma gives a ray `(t_n)` with infinitely many points of `f(Ω)` beyond
  every edge `e_n = (t_n, t_(n+1))`. One-endedness (item 2) then makes the near sides `F_n = A_(e_n)`
  finite.
- The `F_n` increase and exhaust `Ω`, since every vertex of `T` eventually lies on the near side, and
  `|∂F_n| ≤ C′`. So `Ω` is amenable, contradicting item 1.

**Item 6.** Every finite orbit of size `N` is an `ε`-expander (item 1 applied to `ℓ²₀` of the orbit), so
its separation is at least `c(ε)N`. Regular maps are monotone for separation (Benjamini–Schramm–Timár,
recalled). So `c(ε)N ≤ C·sep_Λ(CN)`, and `sep_Λ(n) = o(n)` bounds `N`.

## Consequences for the master route

- **Track B's "Z² first" cannot use the full-group mechanism for inputs.** Over an amenable `P`,
  `[[P ⋉ X]]` never contains an infinite simple Kazhdan group. Gate U over `Z²` must therefore embed
  `H_Γ` into units of `(LC(X, F₂) ⋊ P) ⊗ L` that lie outside `[[P ⋉ X]]`, or `P` must be nonamenable.
  - The G2 calibration over `Z²` is unaffected.
- **F₂ × F₂ passes every test.** It is nonamenable, one-ended, of exponential growth and not virtually
  free. It is also finitely presented and Farrell–Jones, being CAT(0), with Farrell–Jones stable under
  products (recalled). So it is the smallest scaffold not excluded, and the sharp open test is
  `infinite-kazhdan-group-in-wobbling-group-of-product-of-trees`.
- **Kazhdan-type scaffolds.** A torsion-free vertex-regular Ã₂ lattice (Farrell–Jones via CAT(0), Wegner;
  recalled) already hosts infinite Kazhdan groups on free orbits, namely every lattice of its building
  (Corollary 2 of `simple-inputs-in-wobbling-hosts-are-dense-schreier-realizations`).

## Lesson for general BH

Property (T) never forbids a bounded-displacement host outright. It forces the input's Schreier
realizations to be one-ended and uniformly expanding at every scale. That kills exactly the scaffolds with
Følner sets, finite cuts or small growth, and leaves products of trees and higher-rank lattices as the only
candidates. For Kazhdan inputs, gate U is therefore a question about expanding one-ended Schreier graphs
inside one fixed nonamenable, one-ended CAT(0) group.
