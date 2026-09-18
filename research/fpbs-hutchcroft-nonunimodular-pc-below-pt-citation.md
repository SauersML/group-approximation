---
rg: 2
id: fpbs-hutchcroft-nonunimodular-pc-below-pt-citation
kind: route
title: Import Hutchcroft's theorem that p_c is strictly below the tiltability threshold for nonunimodular transitive groups
target: fpbs-hutchcroft-nonunimodular-pc-below-pt
requires: []
---

This is a citation import, not a reproof. The source is T. Hutchcroft,
"Non-uniqueness and mean-field criticality for percolation on nonunimodular
transitive graphs", arXiv:1711.02590v3. The TeX source
(`NonunimodularPercolation_Revised5.tex`, from the arXiv e-print) was read on
2026-09-18. The abstract says the paper was accepted in J. Amer. Math. Soc.
Line numbers refer to that TeX file. The markup is kept as it appears there.

**Modular function (lines 275-276, verbatim).**

> the \textbf{modular function} of $(G,\Gamma)$ is the function
> $\Delta=\Delta_\Gamma :V^2 \to (0,\infty)$ defined by
> \[\Delta(x,y) = \frac{|\stab_y x|}{|\stab_x y|},\]

**Tilted susceptibility (lines 498-499, verbatim).**

> \textbf{tilted susceptibility} $\chi_{p,\lambda}(v)$ to be the expected
> tilted volume of the cluster at $v$, that is,
> \[\chi_{p,\lambda}(v) = \bE_p \left[ |K_v|_{v,\lambda} \right] = \sum_{u\in V} \tau_p(v,u) \Delta^\lambda(v,u).\]

**Thresholds (lines 502 and 506, verbatim).**

> \pcl{\lambda} = p_c(G,\Gamma,\lambda) = \sup\big\{ p \in [0,1] : \chi_{p,\lambda}(v) < \infty \big\}.

> p_t =p_t(G,\Gamma) = \sup \left\{ p \in [0,1] : \chi_{p,\lambda}(v) < \infty \text{ for some $\lambda \in \R$}\right\},

**Symmetry and base-point independence (line 509, verbatim).**

> It is easily seen that these definitions do not depend on the choice of $v$.
> In \cref{sec:meanfieldsusceptibility} we observe that
> $\pcl{\lambda}=\pcl{1-\lambda}$ for every $\lambda\in \R$ and that
> $p_t=\pcl{1/2}$.

**Theorem (lines 518-522, verbatim).**

> \begin{thm}
> \label{thm:pcpt}
> Let $G$ be a connected, locally finite graph and suppose that
> $\Gamma \subseteq \operatorname{Aut}(G)$ is transitive and nonunimodular.
> Then $p_c(G) < p_c(G,\Gamma,\lambda) \leq p_t(G,\Gamma)$ for every
> $\lambda \in (0,1)$.
> \end{thm}

Hutchcroft and Pan, arXiv:2412.15895v1, Section 1, restate the result: "the
main result of [23] is that pc < pt for any connected, locally finite graph
equipped with a quasitransitive nonunimodular group of automorphisms".

This route asserts only that the cited theorem says what the target records.
