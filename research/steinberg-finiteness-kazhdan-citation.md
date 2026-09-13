---
rg: 2
id: steinberg-finiteness-kazhdan-citation
kind: route
title: Import the Steinberg theorem and its finite-presentation input from Ershov and Jaikin-Zapirain
target: steinberg-finite-presentation-and-kazhdan-theorem
requires: []
artifacts:
  - research/artifacts/boone-higman-steinberg-cover-correction-2026-09-08.md
---

Source checked 2026-09-08:
[Ershov--Jaikin-Zapirain, arXiv:0809.4095v2](https://arxiv.org/pdf/0809.4095v2),
Section 6.1, printed page 35.

Theorem 6.2 establishes property (T) for St_n(R), n>=3, when R is
finitely generated. The paragraph following Proposition 6.3 cites
Krstic--McCool, Theorem 3, for finite presentation of St_n(R), n>=4,
when R is finitely presented. The same section explicitly distinguishes
St_n(R) from its elementary quotient and uses it as a finitely presented
cover.

The Krstic--McCool article is *Presenting GL_n(k<T>)*, Journal of Pure
and Applied Algebra 141 (1999), 175--183. Its theorem is verified here
through the explicit statement in the authors' universal-lattice paper;
the original 1999 full text has not been independently read in this turn.
This is a literature import, not a Lean proof.

**Verbatim (review 2026-09-13, un-verify-measure).** arXiv:0809.4095v2 e-print, fetched on MSI, `EL_n0909.tex` lines 2496–2501:

> "By a theorem of Krstić and McCool [Theorem 3]{KrM}, the Steinberg group $St_n(R)$ is finitely presented for any
> $n\geq 4$ and any finitely presented ring $R$, in particular for $R=\mathbb Z\langle x_1,\ldots, x_d\rangle$. […] By
> [Corollary 2]{KrM}, the group $St_3(R)$ is not finitely presented whenever $R$ surjects onto $F[t]$ for some field $F$."

[KrM] is J. Pure Appl. Algebra 141 (1999) 175–183, DOI 10.1016/S0022-4049(98)00022-X. The primary text is still
unread: ScienceDirect served a bot page and the Elsevier API needs a key.
