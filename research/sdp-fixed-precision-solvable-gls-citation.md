---
rg: 2
id: sdp-fixed-precision-solvable-gls-citation
kind: route
title: Import Theorem 1.1 of de Klerk--Vallentin, On the Turing model complexity of interior point methods for semidefinite programming (arXiv:1507.03549), attributed there to Grotschel--Lovasz--Schrijver
target: sdp-fixed-precision-solvable-gls
requires: []
---

Literature import, credited in full.

Etienne de Klerk, Frank Vallentin, *On the Turing model complexity of interior
point methods for semidefinite programming*, arXiv:1507.03549v2 (16 July 2015).
The theorem is due to M. Grotschel, L. Lovasz,
A. Schrijver, *Geometric Algorithms and Combinatorial Optimization*, Springer
1988 (their reference [4]).

Verified from the arXiv PDF, pages 1--2, text extracted on 2026-09-17:

> Theorem 1.1 (Grötschel, Lovász, Schrijver [4]). Consider the semidefinite
> program
> (1) val = inf ⟨C, X⟩, X∈S^n is positive semidefinite, ⟨A_j, X⟩ = b_j for
> j = 1, . . . , m,
> with rational input C, A_1, . . . , A_m, and b_1, . . . , b_m, and where S^n
> denotes the set of n× n symmetric matrices. Denote by
> F = {X∈S^n : X is positive semidefinite, ⟨A_j, X⟩ = b_j for j = 1, . . . , m}
> the set of feasible solutions. Suppose we know a rational point X0∈F and
> positive rational numbers r, R so that
> X0 + B(X0, r)⊆F⊆ X0 + B(X0, R),
> where B(X0, r) is the ball of radius r, centered at X0, in the d-dimensional
> subspace L = {X∈S^n : ⟨A_j, X⟩ = 0 for j = 1, . . . , m}.
> For every positive rational number ǫ > 0 one can find in polynomial time a
> rational matrix X∗∈F such that
> ⟨C, X∗⟩− val ≤ ǫ,
> where the polynomial is in n, m, log2 R/r, log2(1/ǫ), and the bit size of the
> data X0, C, A_1, . . . , A_m, and b_1, . . . , b_m.
> Here ⟨X, Y⟩ = Trace(XY) denotes the trace inner product for symmetric
> matrices, and hence, when we talk about the ball B(X0, r) or B(X0, R) we work
> with the associated Frobenius norm ‖X‖_F = ⟨X, X⟩^(1/2).

Sub- and superscripts were restored from the PDF layout; the words are as
printed.

**Reading of the ball notation.** Since `B(X0, r)` is placed "in the subspace
`L`", the printed inclusion is read as: the Frobenius ball of radius `r` in
`L`, translated to `X0`, lies in `F`, and `F` lies in the corresponding ball
of radius `R`. That is the statement of the claim. Any user of this import
should verify both inclusions in this reading. The only user in the graph,
`spectral-gap-no-output-kill-proof`, verifies them with `X0 = I/k`, `r = 1/k`
and `R = 2Nk`.
