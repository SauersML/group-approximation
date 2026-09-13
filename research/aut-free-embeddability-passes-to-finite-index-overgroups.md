---
rg: 2
id: aut-free-embeddability-passes-to-finite-index-overgroups
kind: claim
title: A group embeds in some Aut(F_n) as soon as one of its finite-index subgroups does, and it then embeds in some Out(F_n) too
distinct_from:
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of the permutational Boone--Higman class under finite-index overgroups; this is closure of the class of subgroups of automorphism groups of finitely generated free groups, proved by inducing the action to a free product of copies.
  outer-covering-lifts-are-virtual-sections: that identifies lifts of outer classes to a finite-index subgroup with virtual sections of Aut to Out; this passes arbitrary faithful actions on free groups up from a finite-index subgroup to the whole group.
  out-free-groups-virtually-embed-in-aut-free-groups: that is an open premise asking for a finite-index subgroup of Out(F_n) inside some Aut(F_m); this elementary lemma shows that premise is equivalent to Out(F_n) itself embedding in some Aut(F_m).
---

**ESTABLISHED.** Elementary (induced actions, as in the Kaloujnine--Krasner
embedding into a wreath product). No novelty is claimed. The derivation is
`aut-free-embeddability-passes-to-finite-index-overgroups-proof`.

Let `A ≠ 1` be a group, `G` a group, `H ≤ G` of finite index `d`, and
`ρ: H → Aut(A)` an injective homomorphism. Write `A^{∗d}` for the free product of
`d` copies of `A`.

1. **Induction.** `G` embeds in `Aut(A^{∗d})`. Each image element permutes the
   `d` factors and maps each factor isomorphically onto a factor.
2. **Free groups.** If `H` embeds in `Aut(F_k)`, `k ≥ 1`, then `G` embeds in
   `Aut(F_{dk})`. Consequently, for any group `G` the following are equivalent:
   `G` embeds in some `Aut(F_n)`; some finite-index subgroup of `G` does; every
   finite-index subgroup of `G` does.
3. **Aut inside Out.** For `n ≥ 1`, `β ↦ [β ∗ id_⟨t⟩]` is an injective
   homomorphism `Aut(F_n) → Out(F_n ∗ ⟨t⟩) = Out(F_{n+1})`. So every group that
   embeds in some `Aut(F_n)` embeds in some `Out(F_m)`.

**Consequences used in the Zaremsky 3.10 region.**
- Embeddability in some `Aut(F_n)` depends only on the commensurability-up class:
  a group and its finite-index subgroups, and extended versus orientation-preserving
  mapping class groups, stand or fall together.
- `out-free-groups-virtually-embed-in-aut-free-groups` at rank `m` is equivalent to
  `Out(F_m)` embedding in some `Aut(F_n)`.
- Torsion cannot obstruct embeddings into automorphism groups of free groups on its
  own: every finitely generated virtually free group embeds
  (`virtually-free-groups-embed-in-aut-free-groups`).

**Scope.** Nothing here passes embeddability in some `Out(F_n)` to finite-index
overgroups. Inducing an outer action choosing representatives is multiplicative
only up to automorphisms acting on each factor by an inner automorphism of that
factor, and such factorwise-inner automorphisms need not be inner in the free
product, so there is no induced homomorphism into `Out(A^{∗d})`.
