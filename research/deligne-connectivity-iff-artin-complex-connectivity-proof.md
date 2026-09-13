---
rg: 2
id: deligne-connectivity-iff-artin-complex-connectivity-proof
kind: route
title: "Proof: cover the Deligne complex by translates of the Deligne complexes of maximal parabolic subgroups; the nerve is the Artin complex"
target: deligne-connectivity-iff-artin-complex-connectivity
requires: []
---

**Literature inputs.** Standard parabolic subgroups are the Artin groups of the induced
subgraphs (van der Lek; arXiv:1211.7339, Theorem 5.4), and `A_X ∩ A_Y = A_{X∩Y}`
(van der Lek, thesis 1983; theorem number not checked in this pass). The nerve theorem
with connectivity: if a simplicial complex is covered by subcomplexes such that every
nonempty intersection of `t` distinct members is `(k − t + 1)`-connected (`t ≥ 1`), then
the complex and the nerve of the cover have isomorphic `π_j` for `j ≤ k` (A. Björner,
*Nerves, fibers and homotopy groups*, J. Combin. Theory Ser. A 102 (2003)). For contractible
intersections, the classical nerve theorem gives a homotopy equivalence.

**Cover.** Assume `W_Γ` infinite, and write `P_s = A_{S∖{s}}`. For a vertex `v = gP_s` of
`Δ(A)`, let `Φ_v ⊆ Φ(A)` be the realization of the cosets contained in `gP_s`. This is a
down-closed subposet, so `Φ_v` is a full subcomplex, and intersections of the `Φ_v` are
realizations of intersections of these subposets.

(a) A spherical coset `hA_U` lies in `gP_s` iff `h ∈ gP_s` and `s ∉ U`. Indeed, if
`hA_U ⊆ gP_s`, then `hP_s = gP_s` and `A_U ⊆ P_s`, so `A_U = A_U ∩ P_s = A_{U∖{s}}`, which
forces `s ∉ U` (the image of `A_{U∖{s}}` in `W` does not contain `s`).

(b) Left translation by `g^{-1}` maps `Φ_v` onto `Φ_{P_s}`, the realization of the cosets
`hA_U` with `h ∈ P_s` and `U ⊆ S∖{s}` spherical. By injectivity these are the spherical
cosets of the Artin group `A_{Γ_{S∖{s}}}`, so `Φ_v ≅ Φ(A_{S∖{s}})`.

(c) The `Φ_v` cover `Φ(A)`. Since `W` is infinite, every spherical `U` is a proper subset
of `S`. A simplex of `Φ(A)` is a chain of cosets with largest element `hA_U`; for any
`s ∉ U` every member of the chain lies in `hA_U ⊆ hP_s`, so the simplex lies in `Φ_{hP_s}`.

(d) Intersections. Let `v_1, …, v_t` be distinct vertices of `Δ(A)`. The cosets lying in
every `v_i` are those lying in `⋂ v_i`. If `⋂ v_i = ∅`, the intersection
`Φ_{v_1} ∩ ⋯ ∩ Φ_{v_t}` is empty. Otherwise the `v_i` have distinct types `R` with
`|R| = t`, `⋂ v_i = xA_{S∖R}` for any common element `x`, and as in (b) the intersection is
isomorphic to `Φ(A_{S∖R})` (a single vertex when `R = S`). So the nerve of the cover is
`Δ(A)`, and every nonempty `t`-fold intersection is a copy of `Φ(A_{S∖R})` with `|R| = t`.

(e) Every `Φ(A_T)` is connected: each coset contains a group element `g = gA_∅`, and `g`
and `gs` both lie in the vertex `gA_{\{s\}}`.

**Item 1.** The nerve theorem needs `t`-fold intersections to be `(k − t + 1)`-connected.
For `t ≤ k` this is the hypothesis. For `t = k + 1` it asks for connectedness, which holds
by (e). For `t ≥ k + 2` it asks only for nonemptiness. So `π_j(Φ(A)) ≅ π_j(Δ(A))` for
`j ≤ k`. For `k = ∞` all intersections are contractible, and the classical nerve theorem
gives `Φ(A) ≃ Δ(A)`.

**Item 2.** (⇐) Show by induction on `|S|` that `Φ(A_Γ)` is `k`-connected. If `W_Γ` is
finite, `Φ(A_Γ)` is a cone. If `W_Γ` is infinite, each `Φ(A_{S∖R})` with `R ≠ ∅` is
`k`-connected by the induction hypothesis, hence `(k − |R| + 1)`-connected. Item 1 gives
`π_j(Φ(A_Γ)) ≅ π_j(Δ(A_Γ)) = 0` for `j ≤ k`; for `k = ∞` it gives a homotopy equivalence
with a contractible complex. (⇒) If every `Φ` is `k`-connected, item 1 applies to every
`Γ` with `W_Γ` infinite, and `Δ(A_Γ)` is `k`-connected. ∎

**Consequences.** The body's `k = ∞` and `k = 2` consequences combine item 1 or item 2
with the Charney–Davis equivalence `Φ(A) ≃` universal cover of the Salvetti complex, with
Theorem 5.5 of arXiv:1211.7339, and, for the ideal, with
`artin-complex-top-homology-is-intersection-of-ideals`. The `k = 1` remark uses Tits'
criterion as cited in the body.
