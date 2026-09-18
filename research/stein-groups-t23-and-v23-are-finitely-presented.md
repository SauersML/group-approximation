---
rg: 2
id: stein-groups-t23-and-v23-are-finitely-presented
kind: claim
title: The Stein groups T_{2,3} and V_{2,3} of piecewise-linear circle homeomorphisms and interval rearrangements are finitely presented
distinct_from:
  pl-rearrangement-groups-have-two-transitive-orbit-actions: that proves the orbit action of V(A,P) is of type (A) exactly when V(A,P) is finitely presented; this is the finite presentation itself for A = Z[1/6] and P = <2,3>.
  stein-group-f23-does-not-embed-in-thompson-v: that is the non-embedding of the interval group F_{2,3} in V; this is finite presentation of the circle and rearrangement versions.
---

**Update (2026-09-18, lane `bh-near-actions`).** The `V_{2,3}` half is proved, with `F_∞`, in the piecewise-linear model
and without Stein's paper: `integral-slope-stein-v-groups-are-k-graph-full-groups` identifies `V_{2,3}` with the full
group of a one-vertex 2-graph and applies Li's finiteness theorem. The `T_{2,3}` half is still open, so this node
stays OPEN.

**OPEN (as a graph node).** `T_{2,3} = T(Z[1/6], <2,3>)` and
`V_{2,3} = V(Z[1/6], <2,3>)`, in the notation of
`pl-interval-and-circle-groups-have-type-a-orbit-actions`, are finitely presented.

## Literature (read from the arXiv TeX on MSI)

Martínez-Pérez--Matucci--Nucinkis, *Cohomological finiteness conditions and
centralisers in generalisations of Thompson's group V*, arXiv:1309.7858, `main.tex`:
- l.293: "The group $V$ has many interesting generalisations such as the
  Higman-Thompson groups $V_{n,r}$, \cite{higman}, Stein's generalisations \cite{stein}
  and Brin's higher dimensional Thompson groups $sV$ \cite{brin1}. All these groups
  contain any finite group, contain free abelian groups of infinite rank, are finitely
  presented and of type $\FP_\infty$".
- l.446: "we give some examples of the groups $V_r(\Sigma)$, which generalise both Brin's
  groups $sV$ \cite{brin1} and Stein's groups $V(l,A,P)$ \cite{stein}. Furthermore, these
  groups satisfy the conditions of Definition \ref{complete} below, and we show in
  Section \ref{fpinfty} that they are of type $\F_\infty.$"
- Example `stein` (l.525–532) builds the Brown--Stein Cantor algebra from a basis
  `{n_1, ..., n_s}` of `P ⊆ Q_{>0}` and writes "We denote the resulting groups
  $V_r(\Sigma)=V_{\{n_1,...,n_s\}}.$"
- Theorem `FPinfty` (l.660): "Let $\Sigma$ be valid, bounded and complete. Then
  $V_r(\Sigma)$ is of type $\F_\infty$."

## Why this node is OPEN

- **The model is not checked.** MMN's groups are automorphism groups of Cantor algebras.
  Their identification with the piecewise-linear groups of `[0,1)` is taken from
  Stein's paper, which was not read. Stein, *Groups of piecewise linear
  homeomorphisms*, Trans. Amer. Math. Soc. 332 (1992) 477--514, DOI
  10.1090/S0002-9947-1992-1094555-4. The AMS PDF returned a challenge page from MSI.
- **`T_{2,3}` has no pinned statement.** Only the `V`-type sentence above was found.
- **What would close it.** A source-checked statement of finite presentation with the
  piecewise-linear definition, or a proof of the Cantor-algebra identification.
