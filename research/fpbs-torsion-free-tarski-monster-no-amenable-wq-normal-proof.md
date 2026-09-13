---
rg: 2
id: fpbs-torsion-free-tarski-monster-no-amenable-wq-normal-proof
kind: route
title: Centralizers of nontrivial elements are the maximal cyclic subgroups, so overlapping conjugates normalize
target: fpbs-torsion-free-tarski-monster-no-amenable-wq-normal
requires:
  - fpbs-osin-ah-groups-not-products-not-torsion
---

Complete proof. `T_0` is nonamenable and torsion-free, and all its proper
subgroups are cyclic. Abelian and virtually cyclic groups are amenable, so
`T_0` is neither. Wq-normality is tested with Peterson--Thom, arXiv:0708.4327,
Lemma `alter`. An infinite `H` is wq-normal in `G` if and only if every
`H <= K < G` has some `g notin K` with `g K g^(-1) ∩ K` infinite.

1. **Two generators.** Choose noncommuting `x` and `y`. Then `<x, y>` is not
   cyclic, so it equals `T_0`.

   **Not acylindrically hyperbolic.** By
   `fpbs-osin-ah-groups-not-products-not-torsion` item 2, an acylindrically
   hyperbolic group contains a non-abelian free subgroup `F`.
   - If `F != T_0`, then `F` is cyclic, a contradiction.
   - If `F = T_0`, take a free basis containing `a` and `b`. Then `<a^2, b>` is
     not cyclic. It lies in the kernel of the map to `Z/2` sending `a` to `1`
     and the other basis elements to `0`, so it is proper. Contradiction.

2. **Nontrivial center.** The center `Z` is proper, since `T_0` is nonabelian,
   so it is cyclic. It is infinite, since `T_0` is torsion-free. For every
   proper `K ⊇ Z` and every `g notin K`, `g K g^(-1) ∩ K ⊇ Z` is infinite. So
   `Z` is wq-normal.

3. **Trivial center.**
   - **Maximal cyclic subgroups.** Every nontrivial cyclic `C` lies in one. The
     union of a chain of cyclic subgroups containing `C` is abelian, so it is
     not `T_0`. It is therefore proper and cyclic, and Zorn's lemma applies. A
     maximal cyclic `M` is proper, because `T_0` is not cyclic.
   - **Centralizers.** Let `1 != y in M`. `Z(y)` is proper, since the center is
     trivial, so it is cyclic. It contains the abelian group `M`, so
     `Z(y) = M` by maximality.
   - **Normalizer.** Suppose `M` is normal. Conjugation gives a homomorphism
     from `T_0` to `Aut(M)`, which has order 2. Its kernel is the centralizer of
     a generator of `M`, which is `M`. So `M` has index at most 2, and `T_0` is
     virtually cyclic, a contradiction. Hence `N(M)` is proper, hence cyclic,
     and so `N(M) = M`.
   - **Malnormal.** Suppose `g M g^(-1) ∩ M` contains some `x != 1`. Then `x`
     and `g^(-1) x g` are nontrivial elements of `M`, so
     `M = Z(x) = g Z(g^(-1) x g) g^(-1) = g M g^(-1)`. So `g in N(M) = M`. Hence
     `g M g^(-1) ∩ M = 1` for every `g notin M`.
   - **No infinite amenable wq-normal subgroup.** An infinite amenable
     `A <= T_0` is proper, since `T_0` is nonamenable, so it is a nontrivial
     cyclic group. Choose a maximal cyclic `M ⊇ A`. Then `A <= M < T_0`, and
     `g M g^(-1) ∩ M` is finite for every `g notin M`. By Lemma `alter`, `A` is
     not wq-normal.

**Membership.** A centerless `T_0` is finitely generated and nonamenable. By
items 1 and 3 it satisfies hypotheses 2 and 3 of
`fpbs-residual-price-one-non-ah-class-nonuniqueness`. So it is a member exactly
when it has fixed price one. Its nontrivial cyclic subgroups are infinite and
amenable, so it is not in part (R0).

**Example.** Source: Ol'shanskii--Sapir, arXiv:math/0208237, `main.tex`, the
LaTeX source fetched on MSI on 2026-09-12. Lines 243-246 read:

> First counterexamples to the von Neumann problem were constructed by
> Ol'shanskii `\cite{OlAmen}`. He proved that the groups with all proper
> subgroups cyclic constructed by him, both torsion-free `\cite{OlTar}` and
> torsion `\cite{OlTar1}` (the so called ``Tarski monsters"), are not amenable.

Lines 9926-9928 give `OlTar` as A. Yu. Ol'shanskii, *An infinite simple
torsion-free Noetherian group*, Izv. Akad. Nauk SSSR Ser. Mat. 43 (1979), no. 6,
1328--1393.
