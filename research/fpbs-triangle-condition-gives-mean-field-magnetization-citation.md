---
rg: 2
id: fpbs-triangle-condition-gives-mean-field-magnetization-citation
kind: route
title: Import Barsky-Aizenman mean-field magnetization under the triangle condition, as stated by Hutchcroft
target: fpbs-triangle-condition-gives-mean-field-magnetization
requires: []
---

Citation import, not a reproof. Source: Tom Hutchcroft, *The L^2 boundedness
condition in nonamenable percolation*, arXiv:1904.05804 (TeX source
`ArmExponent8.tex`, fetched 2026-09-17 from `https://arxiv.org/e-print/1904.05804`).
Markup is transcribed.

* Lines 1358-1371 (Section on the ghost field):
  "For each $v\in V$, $0<p<1$, and $h>0$, we define the \textbf{magnetization}
  \begin{equation} M_{p,h}(v)=\bP_{p,h}(v \leftrightarrow \cG) = \bE_p\left[1-e^{-h|K_v|}\right]. \end{equation}
  [...] It is proven in \cite{MR1127713} (and follows from \cref{exponent:volume}) that if $G$ is
  quasi-transitive and satisfies the triangle condition then
  \begin{equation} \label{exponent:magnetization} M_{p_c,h}(v) \asymp \sqrt{h} \qquad \text{ as $h\downarrow 0$}, \end{equation}
  and in fact the lower bound of \eqref{exponent:magnetization} holds for every quasi-transitive graph \cite{aizenman1987sharpness}.
  (Some aspects of the proof of \cite{MR1127713} are specific to the case of $\Z^d$, see
  \cite[Section 7]{Hutchcroftnonunimodularperc} for an overview of the changes needed to handle arbitrary quasi-transitive graphs.)"
* Line 141 (introduction): "In particular, if $G$ is a connected, locally finite,
  quasi-transitive graph that satisfies the triangle condition then the estimates
  \eqref{exponent:gamma}, \eqref{exponent:theta}, and \eqref{exponent:volume} all hold for every vertex $v$ of $G$."
  The same line continues: "(The lower bounds of \eqref{exponent:gamma},
  \eqref{exponent:volume}, and \eqref{exponent:theta} hold on every quasi-transitive graph
  \cite{aizenman1987sharpness,MR762034}.)"
  Here `exponent:volume` is "$\bP_{p_c}\left( |K_v| \geq n\right) \asymp n^{-1/2}$".

`MR1127713` is D. J. Barsky and M. Aizenman, *Percolation critical exponents
under the triangle condition*, Ann. Probab. 19 (1991). `Hutchcroftnonunimodularperc`
is Hutchcroft, *Non-uniqueness and mean-field criticality for percolation on
nonunimodular transitive graphs*, arXiv:1711.02590, Section 7.
