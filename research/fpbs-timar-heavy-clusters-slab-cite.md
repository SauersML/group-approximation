---
rg: 2
id: fpbs-timar-heavy-clusters-slab-cite
kind: route
title: Import Timar's slab theorem through Hutchcroft's verbatim statement of it
target: fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab
requires: []
---

Citation import, not a reproof. The source is T. Hutchcroft, "Nonuniqueness and
mean-field criticality for percolation on nonunimodular transitive graphs",
arXiv:1711.02590v3, LaTeX source `NonunimodularPercolation_Revised5.tex`,
read on 2026-09-18. The quotes below are verbatim, with line numbers in that
file.

Line 3783 (a proof in Section 8.1, "Different automorphism groups on the tree"):

> A result of Tim\'ar \cite[Theorem 5.5]{timar2006percolation} states that if
> $G$ is a connected, locally finite graph, $\Gamma$ is a transitive
> nonunimodular subgroup of $G$, and $G[p]$ has infinitely many heavy
> clusters almost surely, then there exists a slab such that the open
> subgraph of the slab contains an infinite cluster almost surely.

Lines 291-292 (definition of heavy):

> We say that a set of vertices $K \subseteq V$ is \textbf{heavy} if
> $\sum_{y\in K} \Delta(x,y) =\infty$ for some $x \in V$ (and hence every
> $x\in V$ by \cref{lem:modularsymmetries}, a.k.a.\ the cocycle identity),
> saying that $K$ is \textbf{light} otherwise.

Line 299 (definition of `p_h`):

> p_h=p_h(G,\Gamma) &= \inf\{ p \in [0,1] : G[p] \text{ contains a heavy
> cluster almost surely}\}.

Line 306 (Timar's Lemma 5.2 and the definition of a slab):

> Tim\'ar \cite[Lemma 5.2]{timar2006percolation} showed that for percolation
> clusters (but not for arbitrary sets), being heavy is almost surely
> equivalent to having \textbf{unbounded height}, meaning that
> $\sup_{y\in K}\Delta(x,y)=\infty$, and is also almost surely equivalent to
> having infinite intersection with some set of the form
> $\{ u \in V : e^s \leq \Delta(v,u) \leq e^t \}$ for some $v\in V$ and
> $s<t$, which we call a \textbf{slab}.

Line 315:

> It is clear that if a unique infinite cluster exists then it must be heavy,
> and hence that $p_h(G,\Gamma) \leq p_u(G)$ for every $G$ and $\Gamma$.

Line 516:

> Moreover, it follows from Tim\'ar's characterisation of heaviness
> \eqref{eq:Timarph} that $p_t\leq p_h$. [...] In \cref{subsec:examplestree}
> we show that both equality and strict inequality between $p_t$ and $p_h$
> are possible.

The phrase "subgroup of $G$" in line 3783 means a subgroup of `Aut(G)`, as in
the paper's standing hypotheses. This route asserts only that the cited
source says what the target records.
