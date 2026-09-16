---
rg: 2
id: closed-mcg-twists-map-to-polynomially-growing-outer-autos
kind: claim
title: For genus at least three, every homomorphism from the closed-surface mapping class group, or from a finite-index subgroup, to Out(F_n) sends Dehn twist powers to polynomially growing outer automorphisms
distinct_from:
  rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg: that bounds the rank of a host from dimension; this constrains the image of each Dehn twist under any homomorphism, in every rank.
  some-closed-surface-mcg-embeds-in-no-out-free-group: that asks for a genus with no embedding at all; this is a necessary condition that every homomorphism satisfies, and bordered-surface embeddings show it is not an obstruction by itself.
artifacts:
  - research/artifacts/closed-mcg-twists-polynomial-growth-2026-09-16.md
---

**ESTABLISHED** by `closed-mcg-twists-map-to-polynomially-growing-outer-autos-proof`.
No novelty is claimed.

Let `g ≥ 3`, `n ≥ 0`, and let `φ : MCG(S_g) → Out(F_n)` be any homomorphism, where
`MCG(S_g)` is the orientation-preserving mapping class group of the closed orientable
surface of genus `g`.

1. For every simple closed curve `c ⊂ S_g`, `φ(T_c)` and `φ(T_c)^{-1}` lie in
   `PG(F_n)`, the polynomially growing outer automorphisms (Bestvina--Feighn--Handel:
   some, equivalently every, relative train track representative has no
   exponentially-growing stratum).
2. If `c_1, …, c_r` are pairwise disjoint, every element of
   `φ(⟨T_{c_1}, …, T_{c_r}⟩)` lies in `PG(F_n)`, and some power `N ≥ 1` puts every
   `φ(T_{c_i})^N` in `UPG(F_n)`.
3. More generally, let `Γ ≤ MCG(S_g)` have finite index and `φ : Γ → Out(F_n)` be any
   homomorphism. If `c_1, …, c_r` are pairwise disjoint and `T_{c_i}^{k_i} ∈ Γ` with
   `k_i ≠ 0`, every element of `φ(⟨T_{c_1}^{k_1}, …, T_{c_r}^{k_r}⟩)` lies in
   `PG(F_n)`, and some positive power of each `φ(T_{c_i}^{k_i})` lies in `UPG(F_n)`.

The engine is a statement about `Out(F_n)` alone: *if `ψ` is central in a subgroup
`D ≤ Out(F_n)` and some positive power of `ψ` lies in `[D, D]`, then `ψ ∈ PG(F_n)`.*
A Dehn twist in genus at least three is central in the image of the mapping class
group of its complement (or of its genus-at-least-two side) and is a commutator
product there, by the lantern relation. For item 3, the transfer to a finite-index
normal subgroup of that image puts a power of the twist in the commutator subgroup of
the smaller group.

Item 3 is the form that matters for Aut hosts, where embeddability is shared by a
group and its finite-index subgroups
(`aut-free-embeddability-passes-to-finite-index-overgroups`).

**Scope.** This is a necessary condition on any embedding asked for in
`every-closed-surface-mcg-embeds-in-some-out-free-group`, the analogue for
`Out(F_n)` of Bridson's theorem that Dehn twists act elliptically in semisimple
actions on CAT(0) spaces (recalled as a template; not re-read, and not used in the
proof). It does not by itself obstruct an embedding: in the
bordered group `MCG(S_{g,1})`, which embeds in `Aut(F_{2g})` and so in
`Out(F_{2g+1})`, Dehn twists act with linear growth, and the same lantern argument
applies there.
