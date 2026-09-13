---
rg: 2
id: magnus-embedding-f-over-n-prime-citation
kind: route
title: Import the Magnus embedding as stated by Myasnikov, Roman'kov, Ushakov and Vershik
target: magnus-embedding-f-over-n-prime-into-wreath-product
requires: []
---

Literature import. W. Magnus, "On a theorem of Marshall Hall", Ann. of Math. 40
(1939). The primary source was **not** read. The statement is taken from
A. Myasnikov, V. Roman'kov, A. Ushakov and A. Vershik, "The word and geodesic
problems in free solvable groups", Trans. AMS 362 (2010), arXiv:0807.1032. Their TeX
source `freesol_WP_30.tex` was read on MSI on 2026-09-13; the passage is l.278--308.
Verbatim:

> "Let $G = F/N$ and $\mathbb{Z}G$ the group ring of $G$ with integer coefficients.
> By $\mu:F \rightarrow G$ we denote the canonical factorization epimorphism, as well
> its linear extension to $\mu: \mathbb{Z}F \rightarrow \mathbb{Z}G$. Let $T$ be a
> free (left) $\mathbb{Z}G$-module of rank $r$ with a basis $\{t_1, \ldots, t_r\}$.
> Then the set of matrices $M(G) = \left(\begin{array}{ll} G & T\\ 0 & 1
> \end{array}\right)$ [...] forms a group with respect to the matrix multiplication.
> It is easy to see that the group $M(G)$ is a discrete wreath product
> $M(G) = A_r wr G$ of the free abelian group $A_r$ and $G$."

> "In \cite{Magnus:1939} Magnus showed that the homomorphism $\phi:F \rightarrow
> M(G)$ defined by $x_i \rightarrow \left(\begin{array}{ll} x_i^\mu & t_i\\ 0 & 1
> \end{array}\right), \ i = 1, \ldots, r,$ satisfies $\ker \phi = N^\prime$. It
> follows that $\phi$ induces a monomorphism $\psi: F/N^\prime \hookrightarrow
> M(F/N),$ which is now called the {\em Magnus embedding}."

Earlier in the same subsection, l.268--276: "$S_{r,d} = F_r / F_r^{(d)}$ is a {\em
free solvable group} of rank $r$ and class $d$", with
"$F^{(d)} = [F^{(d-1)}, F^{(d-1)}]$".

The same paper, l.385--390, quotes Fox's theorem: for `u ∈ F`, every
`(∂u/∂x_i)^μ = 0` if and only if `u ∈ [N,N]`. Their l.414: "the faithfulness of the
Magnus embedding is, in fact, equivalent to the Fox Theorem above."

The identification of the matrix group with the restricted regular wreath product
("discrete wreath product") is checked by hand in the target node.
