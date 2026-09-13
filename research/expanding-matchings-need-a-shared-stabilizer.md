---
rg: 2
id: expanding-matchings-need-a-shared-stabilizer
kind: claim
title: Near-equivariant bijections between expanding B-sets need coinciding point stabilizers, so congruence vertex models of the dyadic amalgam cost a Selberg-sized defect
distinct_from:
  unamplified-iwahori-sheets-have-two-thirds-defect: that computes the defect of the three-point sheets only; this bounds every bijection between arbitrary principal-congruence vertex models at any 2-adic depth and any multiplicities.
  random-iwahori-actions-resist-nielsen-matching: that is an entropy bound for independent random edge actions; this is a deterministic spectral bound for structured congruence actions, where counting says nothing.
  homogeneous-k-orbit-factor-has-no-finite-a-refinement: that excludes exact common finite levels; this excludes approximate gluing of any two congruence levels with a uniform constant.
  dyadic-radial-shell-couplings-have-one-third-boundary: that is a boundary bound for mixtures of tree spheres; this is a spectral bound for congruence frame models, including those coming from compact lattice quotients.
---

**ESTABLISHED (unreviewed).**

**1. Lemma G.** Let `B` be a group with a finite generating set `S`, and let `V_0`, `V_1` be finite
`B`-sets with `|V_0| = |V_1|`. Call a `B`-orbit `O` of the diagonal action on `V_0 × V_1`
*coincident* if `Stab_B(x) = Stab_B(y)` for `(x,y) ∈ O`. Suppose every non-coincident orbit is an
`h`-expander: `Σ_(s∈S) |{u ∈ U : su ∉ U}| >= h|U|` whenever `U ⊆ O` and `|U| <= |O|/2`. Then every
bijection `τ : V_0 → V_1` satisfies

```text
Σ_(s∈S) |{v : τ(sv) != sτ(v)}|  >=  h · |{v : (v, τv) lies in a non-coincident orbit}|.   (G1)
```

The proof takes the graph of `τ` inside a single diagonal orbit. The graph is injective on both
projections. Unless the two stabilizers coincide, the orbit is at least twice as large as either
projection, so the graph occupies at most half of it and pays its Cheeger boundary.

**2. Dyadic congruence vertex models.** Let `C_0 = PSL_2(Z)` and `g = diag(1,2)`. Put
`C_1 = gC_0g^(-1)` (the stabilizer of the adjacent tree vertex in `PSL_2(Z[1/2])`) and
`B = C_0 ∩ C_1 = PΓ_0(2)` with a finite generating set `S`. Write `Γ(L)` for the principal
congruence subgroup of `C_0`, and `Γ_1(L) = gΓ(L)g^(-1)`. Let `V_0` be a finite `C_0`-set with
every orbit of the form `C_0/Γ(L)`, and `V_1` a finite `C_1`-set with every orbit of the form
`C_1/Γ_1(L')`. The levels may vary from orbit to orbit and the multiplicities are arbitrary. Assume
`|V_0| = |V_1|`. There is `h_S > 0`, depending only on `S`, such that every bijection
`τ : V_0 → V_1` has

```text
Σ_(s∈S) |{v : τ(sv) != sτ(v)}|  >=  h_S · |{v : v or τ(v) lies in an orbit of even level}|.   (G2)
```

Only pairs of odd-level orbits of equal level can be glued for free. Those are exactly the pieces
on which the `B`-actions extend to honest actions of `PSL_2(Z[1/2])`. There the vertex group
surjects onto the image of the whole group, and the co-dense `(τ)` outlier bound
(`codense-tau-coset-soficity-forces-permutation-instability`) removes every separating label.

**Consequence for the programs of this region.**
* **Frame microstates.** The depth-`M` frame spaces of a compact quotient `PSL_2(Q_2)/Λ` are, as
  `C_0`-sets and `C_1`-sets, disjoint unions of `C_0/Γ(2^M)` and of `C_1/Γ_1(2^M)`. By `(G2)`,
  **every** bijection between the two frame systems, at any depths and with any multiplicities, has
  Hamming defect at least `h_S` on the edge generators. So the microstates asked for in
  `dyadic-homogeneous-quotient-admits-topological-microstates` cannot be glued from congruence frames
  of both vertices. Their vertex-group orbits must contain a macroscopic proportion of
  **non-congruence** orbits, and the diagonal orbits must fail the Selberg gap.
* **Random lifts.** `dyadic-amplified-edge-random-lifts-exist` asks for exact vertex actions
  amplified internally. By `(G2)` the amplification cannot be congruence on both sides, and odd-level
  amplification carries no label. The surviving amplifications have non-expanding
  diagonal `B`-orbits.

**Model tests.** If `V_0 ≅ V_1` as `B`-sets, every orbit meeting the graph of the isomorphism is
coincident, and `(G1)` correctly gives nothing. For the frame systems no pair of stabilizers
coincides, as the unipotent-valuation check in the proof shows, and the bound is uniform in the depth.
