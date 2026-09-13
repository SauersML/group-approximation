---
rg: 2
id: rybak-general-type-limit-set-topologically-free-iff-mif
kind: claim
title: "Rybak: for a general type action on a hyperbolic space that is faithful on the limit set, topological freeness on the limit set is equivalent to being MIF"
distinct_from:
  fp-simple-kac-moody-lattices-are-mif: that imports Rybak's application to finitely presented simple Kac--Moody groups; this imports the general criterion it rests on, for any group with such an action.
---

**ESTABLISHED (literature import).** Suppose a group `G` acts by isometries on a
hyperbolic space `S`, the action is of general type, and the induced action of `G`
on the limit set `Λ_S(G)` is faithful. Then `G` is mixed-identity-free exactly when
the action of `G` on `Λ_S(G)` is topologically free.

**Source.** E. Rybak, *Boundary dynamics, triple transitivity, and mixed identities
in weakly hyperbolic groups*, arXiv:2605.14159v3, TeX source fetched on MSI on
2026-09-13 (`/scratch.global/sauer354/km-ht/2605.14159.d/main.tex`), Theorem
`real main theorem`, l.946--952:

> "Suppose that an action of a group $G$ on a hyperbolic space $S$ is of general
> type and the induced action on $\Lambda_S(G)$ is faithful. Then the following are
> equivalent: (1) $G$ is MIF. (2) The induced action of $G$ on $\Lambda_S(G)$ is
> topologically free."

Definitions used there, from the same source:
- l.180: "an action of a group $G$ on $X$ by homeomorphisms is {\it topologically
  free} if the set of fixed points $\Fix_X(g)$ of every non-trivial element
  $g \in G$ has empty interior."
- l.358: "The \textit{limit set} $\Lambda_S(G)$ of $G$ is defined as the
  intersection of the closure of $Gs$ in $\widehat S$ with $\partial S$."
- l.183: "A weakly hyperbolic group $G$ is called {\it lim-free} if it admits a
  general type action on a hyperbolic space $S$ such that the induced action on
  $\Lambda_S(G)$ is topologically free."

The proof of (2) ⇒ (1) (l.962--985) chooses a limit point moved by every
coefficient of a given mixed word and plays ping-pong with a loxodromic element.
Not re-verified here, and no independent review.

Citation: `rybak-limit-set-mif-criterion-citation`.
