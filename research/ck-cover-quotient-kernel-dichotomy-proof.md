---
rg: 2
id: ck-cover-quotient-kernel-dichotomy-proof
kind: route
title: Factor through the image of a normal subgroup and apply the matrix double-coset obstruction
target: ck-cover-quotient-kernel-dichotomy
requires: [ck-quotient-corner-has-infinite-bi-index, proper-normal-subgroups-miss-the-normally-generating-core]
artifacts:
  - research/artifacts/boone-higman-cover-kernel-dichotomy-2026-09-08.md
---

The normal-generator/simple-core lemma gives M intersect S=1, so
S_M is isomorphic to S. Surjectivity of rho makes N=rho(M) normal
in Q, and there is a surjection

    Gamma/M -> Q/N,     gamma M |-> rho(gamma) N.

Its image of S_M is the inherited matrix corner D_N. If N is proper,
ck-quotient-corner-has-infinite-bi-index gives infinitely many D_N double
cosets in Q/N. The displayed map induces a surjection of double-coset
sets, so S_M also has infinite bi-index in Gamma/M. This proves (1).

Consequently finite bi-index forces rho(M)=Q. For every gamma in Gamma,
choose m in M with rho(m)=rho(gamma). Then m^-1 gamma lies in K,
so Gamma=MK. The quotient map restricted to K is therefore onto
Gamma/M, with kernel K intersect M. This proves (2).

If M is maximal proper normal, MK is a normal subgroup containing M.
Either MK=M, so K is contained in M and Gamma/M is the corresponding
simple quotient Q/N; or MK=Gamma, which gives rho(M)=Q and the
surjection from K just established. These alternatives are mutually
exclusive since K contained in M implies N is proper. This proves (3).

A quotient of a solvable group is solvable, and no nontrivial perfect
group embeds in a solvable group. The infinite simple S is perfect.
A quotient of a locally finite group is locally finite; if it is also
finitely generated, it is finite. Every Gamma/M here is finitely generated
and contains the infinite S. Thus neither type of K can surject onto
Gamma/M for a proper M. Apply (2) and (3) to obtain (4).

No finite presentation, centrality, or normal-structure classification of
the elementary group is used in this argument.
