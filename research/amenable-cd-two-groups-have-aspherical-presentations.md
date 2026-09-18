---
rg: 2
id: amenable-cd-two-groups-have-aspherical-presentations
kind: claim
title: Every finitely generated amenable group of cohomological dimension 2 has an aspherical presentation on finitely many generators (equivalently, a free second syzygy)
distinct_from:
  amenable-free-top-syzygy-forces-type-fp: that proves this statement is equivalent to Kropholler's question in dimension 2 and that no counterexample has such a presentation; this is the open statement itself
  amenable-cd-two-rational-group-algebras-are-coherent: that is the ring form of Kropholler's question in dimension 2; this is its presentation form, a statement about one projective module over Z[G]
  eilenberg-ganea-or-whitehead-is-false: that concerns geometric dimension of cd-2 groups in general; this asks for an aspherical 2-complex with finite 1-skeleton, which for amenable groups is already equivalent to finite presentability
---

**OPEN.** Let `G` be a finitely generated amenable group with `cd G = 2`. Then some finite
generating set `x_1, …, x_d` of `G` gives a free second syzygy
`P = ker(Z[G]^d → Z[G], e_j ↦ x_j − 1)`. In the geometric form, `G` has an aspherical presentation
`⟨x_1, …, x_d | R⟩`, with `R` a priori of any cardinality.

By `amenable-free-top-syzygy-forces-type-fp` (item 3(c)), both forms are equivalent to
Kropholler's question for groups of cd at most 2. The presentation form implies the syzygy form
directly. Both imply finite presentability with `|R| = d − 1`, by item 1 there.

**Shape.** For a counterexample `G`, the projective `P` is countably generated, not finitely
generated, and `L²`-small: `U(G) ⊗ P` embeds in `U(G)^d`. It has no free direct summand of rank
more than `d − 2`, and `P ⊕ Z[G]^(∞)` is free (Eilenberg swindle). So the statement is a Bass-type
"big syzygies are free" assertion for `Z[G]`, restricted to `L²`-small syzygies of amenable groups
of cd 2.
