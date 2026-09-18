---
rg: 2
id: sl-n-q-is-colimit-of-lattice-stabilizers
kind: claim
title: SL_n(Q) is the colimit of the stabilizers of squarefree diagonal lattices over the restricted product of Bruhat-Tits chambers
distinct_from:
  gl-n-q-generated-by-gl-n-z-and-prime-dilations: that gives generators only; this gives a complete presentation as a colimit of copies of SL_n(Z) and their intersections, uniform in the prime.
  elementary-groups-over-polynomial-s-integers-are-fp: that is finite presentation of one E_n(Z[1/m][t]) through Steinberg groups and K_2; this presents the non-finitely-generated SL_n(Q) through lattice stabilizers, with no K_2 input.
artifacts:
  - research/artifacts/gq-gq-k2-q-uniformity.md
  - research/artifacts/gq-referee-b-sl-n-q-is-colimit-of-lattice-stabilizers.md
---

**ESTABLISHED (2026-09-17)** through `sl-n-q-is-colimit-of-lattice-stabilizers-proof`.
*Reviewed (gq-referee-b, citation and hypothesis lens):* PASS, conditional on
amendments A1 and A2, which are made in the route. See
`research/artifacts/gq-referee-b-sl-n-q-is-colimit-of-lattice-stabilizers.md`.
The two literature inputs were read only through secondary transcriptions; the
route marks which. For `n = 2` and one prime this is Serre's amalgam
`SL_2(Z[1/p]) = SL_2(Z) *_{Γ_0(p)} SL_2(Z)^{diag(1,p)}` (Serre, *Trees*, Ch. II
§1.4, not read at source). No novelty is claimed: this is the standard
presentation of an `S`-arithmetic group from its action on a product of
buildings, passed to the union over all `S`.

**Statement.** Let `n >= 2`. For a vector `c = (c_1,...,c_n)` of squarefree
positive integers with `1 = c_1 | c_2 | ... | c_n` put
`L_c = c_1 Z ⊕ ... ⊕ c_n Z` and `Γ_c = SL(L_c) = diag(c) SL_n(Z) diag(c)^-1`.
Put `k_p(c) = #{i : p | c_i} in {0,...,n-1}`; then `L_c ⊗ Z_p = Z_p^(n-k) ⊕ (pZ_p)^k`
with `k = k_p(c)`, a vertex of the standard chamber `Δ_p` of the building of
`SL_n(Q_p)`, and `c ↔ (k_p(c))_p` identifies these `c` with the vertices of the
restricted product `∏'_p Δ_p`.
A *cell* is a family `F = (F_p)_p` of nonempty subsets `F_p ⊆ {0,...,n-1}` with
`F_p = {0}` for almost all `p`; its vertices are the `c` with `k_p(c) in F_p` for
all `p`, and `Γ_F = ∩_{c vertex of F} Γ_c`.

Then `SL_n(Q)` is the colimit (amalgamated sum) of the diagram of groups
`{Γ_F}` indexed by the cells `F`, ordered by reverse inclusion, with inclusion
maps.

**Shape of the diagram.** The *index poset* is the restricted product over
primes of the face poset of one `(n-1)`-simplex, the same for every `p`. The
*groups* are not products: `Γ_F = SL_n(Q) ∩ ∏_p P_{F_p}`, where `P_{F_p}` is the
pointwise stabilizer in `SL_n(Q_p)` of the face `F_p` of `Δ_p` and
`P_{{0}} = SL_n(Z_p)`. Each `Γ_F` is a congruence subgroup of a conjugate of
`SL_n(Z)`, cut out by conditions modulo the primes `p` with `F_p ≠ {0}`.

**Equivalent vertex–edge form.** The colimit equals the amalgam of the vertex
groups `Γ_c` along the edge groups `Γ_{F(c,c')}`, where `c < c'` runs over
comparable pairs inside a cell and `F(c,c')` is the smallest cell containing
both (route, step 4).
