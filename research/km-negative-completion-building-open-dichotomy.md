---
rg: 2
id: km-negative-completion-building-open-dichotomy
kind: claim
title: For 2-spherical Kac--Moody groups over fields with at least four elements, the building-open dichotomy and its high-transitivity consequences also hold for the negative completion
distinct_from:
  km-building-open-subgroups-have-infinite-bi-index: that proves the double-coset dichotomy for subgroups open in the positive building topology and leaves the negative one unclaimed; this transfers it to the negative building topology through a Chevalley involution exchanging the two halves of the twin building.
  km-building-open-subgroups-have-infinite-ht-orbits: that constrains orbits of positively building-open subgroups in highly transitive actions; this gives the same constraints for negatively building-open subgroups, such as the opposite Borel subgroup.
---

**ESTABLISHED** through `km-negative-completion-building-open-dichotomy-proof` (lane
bh-free-24, 2026-09-18; a short transport argument, not reviewed). No novelty is claimed.

**Setting.** `Λ` is a group with an `F`-locally split root group datum `{U_α}_{α∈Φ}` of
irreducible 2-spherical type `(W,S)` with `W` infinite, over a field `F` with `|F| ≥ 4`.
Split minimal Kac--Moody groups over `F_q`, `q ≥ 4`, are examples; so are the type
`(2,4,6)` lattices `Λ_q` of `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`. Call
`M ≤ Λ` **negatively building-open** if it contains the trace `Λ ∩ V` of an open subgroup
`V` of the completion `G_-` of `Λ` in the negative building topology. Equivalently, it
contains the pointwise fixator in `Λ` of a finite set of chambers of the negative building
`X_-`. Examples are `B_-`, the negative standard parabolics and their finite-index
subgroups.

**Statement.**
- **(A−)** `[Λ : M] < ∞` or `|M\Λ/M| = ∞` for every negatively building-open `M`.
- **(A''−)** The same holds in `Λ/N` for `N ⊴ Λ` with `N ⊆ Z_Λ(Λ^†)`, for every subgroup
  containing the image of a negatively building-open subgroup.
- **(a−)--(d−)** Items (a), (b), (b'), (c), (d) of
  `km-building-open-subgroups-have-infinite-ht-orbits` hold with `G_-` in place of `G`.
  In particular, in any highly transitive action of `S_q = Λ_q/Z`, the images of `B_+`,
  `B_-`, and of the pointwise fixators of finite sets of chambers in either half of the
  twin building, together with all their finite-index subgroups, have only infinite orbits.

**The mechanism.** A Chevalley involution `θ` of `Λ` (De Medts--Gramlich--Horn,
arXiv:0709.3466v2) satisfies `θ(U_α) = U_{−α}` and `θ(B_+) = B_-`, and acts trivially on
`W`. So it is a topological isomorphism from `Λ` with the negative building topology to
`Λ` with the positive one. It carries negatively building-open subgroups to positively
building-open ones, and every statement above to its proved positive version.

**Scope.**
- **Pinned only for 2-spherical types with `|F| ≥ 4`.** That is the hypothesis of the
  existence lemma used.
- **Other types are not claimed.** For other split Kac--Moody groups, De Medts--Gramlich--Horn
  (TeX l.186) state that a sign automorphism gives such an involution, citing
  Caprace--Mühlherr §8.2. That section was not read.
