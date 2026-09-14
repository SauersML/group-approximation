---
rg: 2
id: clr-profinite-presentations-and-csp-over-fq-t
kind: claim
title: Bounded presentations of Chevalley groups over F_q[t,1/t], their profinite transfer to F_q[[t]], and the congruence subgroup property with trivial kernel
distinct_from:
  sl3-fq-t-profinite-completion-is-finitely-presented: that is the consequence for the one-place group SL_r(F_q[t]), which also needs the product decomposition of its adelic completion; this only imports the three cited statements.
artifacts:
  - research/artifacts/hl-hyperlinear-vs-sofic-2026-09-13.md
---

**ESTABLISHED by citation.** Capdeboscq--Lubotzky--Rémy, *Presentations: from
Kac--Moody groups to profinite and back*, arXiv:1508.00526, file
`ProfinitePresentations_August28.tex` from the arXiv e-print, read on MSI on
2026-09-13. The three statements below are quoted verbatim from that source.

**(C1) Theorem C** (attributed there to Capdeboscq, `\cite{kn::Cap}`, TeX
l.288--294):

> There exists a constant $C>0$ such that for any simple, simply connected,
> Chevalley group scheme ${\bf G}$ of rank $\geqslant 2$ and for any prime
> power $q \geqslant 4$, the group $G={\bf G}(\mathbf{F}_q[t,t^{-1}])$ admits
> a presentation $\Sigma(G)$ with $D_{\Sigma(G)}$ generators and
> $R_{\Sigma(G)}$ relations satisfying $D_{\Sigma(G)}+R_{\Sigma(G)} \leqslant C$.

**(C2) Proposition 1.2** (`prop::AL`, TeX l.307--311):

> Assume that the rank of the simple, simply connected, Chevalley group
> ${\bf G}$ is $\geqslant 2$ and that the arithmetic group
> ${\bf G}(\mathbf{F}_q[t, t^{-1}])$ has a presentation with $d$ generators
> and $r$ relations. Then for any $e \geqslant 1$, the group
> ${\bf G}(\mathbf{F}_{q^e}[[t]])$ has a profinite presentation with $d$
> generators and $r+1$ relations.

**(C3) Congruence subgroup property** (`th:CSP`, TeX l.348--354; CLR cite
Raghunathan, Prasad--Raghunathan and Margulis, VIII.2.16):

> Let ${\bf G}$ be a simply connected Chevalley group, let $k$ be a global
> field and let $S$ be a finite set of places of $k$. Let $A$ denote the ring
> of $S$-integers in $k$ and for each $v \in S$, let $k_v$ be the
> corresponding completion of $k$. We set
> ${\rm rk}_S({\bf G}) = \sum_{v \in S} {\rm rk}_{k_v}({\bf G})$ and assume
> that ${\rm rk}_S({\bf G}) \geqslant 2$. Then the kernel of the map
> $\pi : \widehat{{\bf G}(A)} \to \overline{{\bf G}(A)}$ is cyclic; it is even
> trivial whenever $S$ contains a non-Archimedean place.

Here $\overline{{\bf G}(A)}$ is the $S$-congruence completion. In the proof of
Proposition 1.2 (TeX l.341--343) CLR identify it with ${\bf G}(\widehat{A})$:

> Since there is no place of ${\bf F}_q(t)$ at which ${\bf G}$ is anisotropic
> and since ${\bf G}$ is simply connected, strong approximation \cite{Prasad}
> implies that the $S$-congruence completion $\overline{{\bf G}(A)}$ is
> described by means of the $S$-ad\`eles $\mathbf{A}_S$ of ${\bf F}_q(t)$.

**Trust surface.** Theorem C is imported by CLR from Capdeboscq; the
congruence subgroup theorem and strong approximation are imported by CLR from
Raghunathan, Prasad--Raghunathan, Margulis and Prasad. None of those primary
sources was read here.

DERIVATION
clr-profinite-presentations-over-fq-t-citation
