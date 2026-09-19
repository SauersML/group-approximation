---
rg: 2
id: co-amenable-hosts-inherit-the-relative-schreier-gate
kind: claim
title: A co-amenable subgroup constrains every subgroup of its host - the coset mean restricts, so no group with a positive H-relative Schreier-Cheeger constant embeds in the host
distinct_from:
  co-amenable-subgroups-transfer-hyperfinite-orbit-relations: that transfers hyperfiniteness of a measured orbit relation from the co-amenable subgroup up to the ambient group; this restricts the coset mean down to arbitrary subgroups of the ambient group and reads off a purely combinatorial Cheeger obstruction, with no measure, no orbit relation and no Connes-Feldman-Weiss.
  fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap: that turns failure of co-amenability of a subgroup into a spectral gap for its own Schreier operator; here co-amenability of H in G is the hypothesis, and the conclusion restricts which groups can embed in G at all.
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that is the classical fact that property (T) of the whole group forbids proper co-amenable subgroups; item 4 here constrains Kazhdan subgroups of G that are neither normal nor of finite index, and assumes nothing about G.
  rokhlin-maximality-ascends-co-amenable-subgroups: that ascends a Rokhlin-entropy property from a co-amenable subgroup to the group; this descends a restriction from the group to all of its subgroups.
  left-right-sofic-closed-under-co-amenable-overgroups: that ascends soficity along a co-amenable inclusion; this is a downward constraint on the subgroup lattice of the host and is not a permanence property.
  thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived: that analyses invariant means on F-sets and their stabilizer IRS inside F; this analyses the restriction of the mean on G/H to subgroups of G and never looks at the IRS of H.
---

**ESTABLISHED.** Let `G` be a countable group and `H ≤ G` co-amenable: there is a `G`-invariant
mean `m` on `ℓ^∞(G/H)` (Monod's definition, arXiv:1209.5229, `vn_pnas3.tex` l.371). Let `Λ ≤ G`
be any subgroup with a finite generating set `S`, and for `g ∈ G` write

  `L_g := Λ ∩ g H g^{-1}`,

the stabilizer in `Λ` of the point `gH ∈ G/H`. Each `L_g` is isomorphic to a subgroup of `H`.

**0. Restriction.** `m` is in particular `Λ`-invariant, so the `Λ`-set `G/H` carries a
`Λ`-invariant mean. Equivalently (Følner's criterion for actions, proved in the route) for every
`ε > 0` there is a finite nonempty `A ⊆ G/H` with `|sA Δ A| < ε|A|` for all `s ∈ S`; equivalently
`1_Λ ≺ ℓ^2(G/H)`.

**1. The gate.** For a group `Λ` with finite generating set `S` and a class `𝒮` of subgroups of
`Λ`, put

  `κ(Λ, S, 𝒮) := inf { h(Sch(Λ, L, S)) : L ∈ 𝒮 }`,

where `Sch(Λ, L, S)` is the Schreier graph of `Λ` on `Λ/L` with respect to `S` and `h` is its
edge-Cheeger constant. Let `𝒮_H(Λ)` be the set of subgroups of `Λ` that are isomorphic to a
subgroup of `H`. Then

  **if `κ(Λ, S, 𝒮_H(Λ)) > 0` for some finite generating set `S`, then `Λ` is not isomorphic to any
  subgroup of `G`.**

The invariant is the *`H`-relative Schreier-Cheeger constant* `κ_H(Λ) := κ(Λ, S, 𝒮_H(Λ))`, and the
step at which every candidate dies is the restriction in item 0: the `Λ`-orbits of `G/H` are the
`Λ`-sets `Λ/L_g` with `L_g ∈ 𝒮_H(Λ)`, so a uniform Cheeger bound on that class contradicts the
Følner sets that the mean produces.

**2. Free subgroups ascend.** If `H` has no non-abelian free subgroup then neither does `G`.
(Concretely `κ_H(F_2) ≥ 2` for the standard basis: every subgroup of `F_2` embeddable in `H` is
free of rank `≤ 1`, and every Schreier graph of `F_2` over a trivial or infinite cyclic subgroup
has `|∂A| ≥ 2|A|`.)

**3. Trivially cut subgroups are amenable.** If `Λ ≤ G` satisfies `L_g = 1` for all `g ∈ G`, then
`Λ` is amenable. In particular, if `H` is torsion-free then every torsion subgroup of `G` is
amenable.

**4. Kazhdan subgroups.** If `Λ ≤ G` has property (T), then some `L_g` has finite index in `Λ`.
Hence if no infinite subgroup of `H` has (T) — for instance if `H` has the Haagerup property —
then no infinite subgroup of `G` has (T).

**5. Dichotomy for a non-amenable subgroup.** Let `Λ ≤ G` be non-amenable. Then either some `L_g`
is non-amenable — so `H` contains a non-amenable subgroup, hence `H` is non-amenable — or every
`L_g` is amenable and there is a sequence `g_n ∈ G` with

  `h(Sch(Λ, L_{g_n}, S)) → 0`,

while no single `L_{g_n}` is co-amenable in `Λ`. So the conjugates of `H` must cut `Λ` into
amenable subgroups that are *asymptotically* co-amenable in `Λ` without ever being co-amenable.

**6. Non-amenable quotients of a co-amenable pair.** If `π : G ↠ Q` then `π(H)` is co-amenable in
`Q`. So a host cannot be simplified: every non-amenable quotient of `G` carries a co-amenable copy
of a quotient of `H`.

**Why this is not the classical normal-subgroup permanence.** The familiar statement is: if
`N ⊴ G` with `G/N` amenable and `N` has no free subgroup, then `G` has none. That proof uses
normality twice (to form `Λ/(Λ ∩ N)` and to know it is amenable). Co-amenability does **not** pass
to intermediate subgroups (Monod and Popa, *On co-amenability for groups and von Neumann
algebras*, C. R. Math. Acad. Sci. Soc. R. Can. 25 (2003) 82-87), so items 1-5 are not corollaries
of the normal case; the proof works directly with the Schreier graphs of the stabilizers.

**Sharpness.** The hypothesis of item 2 cannot be dropped, and item 1 really does need a *uniform*
bound over `𝒮_H(Λ)`. Take `H = [F_2, F_2] ≤ G = F_2`. Here `H` is co-amenable in `G`, because the
Schreier graph is the Cayley graph of `Z^2`, which is amenable. Taking `Λ = G = F_2` (non-amenable)
we get `L_g = H` for every `g`, and `h(Sch(F_2, H, S)) = h(Z^2) = 0`: the infimum in item 1 is `0`,
as it must be. This is the first branch of item 5 — `L_g` is itself non-amenable, being free of
infinite rank — and it is also why item 2 assumes that `H` has no non-abelian free subgroup.

Proof route: `co-amenable-hosts-relative-schreier-gate-proof`.
