---
rg: 2
id: dln-galois-symmetry-of-modular-twists-citation
kind: route
title: Import the Galois symmetry of modular data from Dong--Lin--Ng
target: dln-galois-symmetry-of-modular-twists
requires: []
---

This imports a published result; nothing is reproved here. The source is C. Dong, X. Lin, S.-H. Ng,
*Congruence property in conformal field theory*, Algebra & Number Theory 9 (2015), no. 9, 2121--2166,
arXiv:1201.6644v7 (27 Oct 2015).
- The PDF was fetched on 2026-09-20 and its text was extracted with `pypdf`.
- The quotations below are verbatim from that extracted text. Page numbers are those of the arXiv PDF.
- Extraction glyphs are normalized as follows:
  - `˜s` is written `s~`;
  - `ˆσ` is written `sigma^`;
  - `ǫσ` is written `eps_sigma`.

**Section 1.3, page 7 (definition and finite order).**

> A modular tensor category over k (cf. [Tu, BK]), also simply called a modular category, is a braided
> spherical fusion category A over k such that the S-matrix of A defined by
> s~_ij = ptr(c_(Vj,Vi*) ∘ c_(Vi*,Vj)) is non-singular, where Vj denotes an object in the class j ∈ Π_A.
> In this case, the associated ribbon structure θ is of finite order N (cf. [Va, BK]). Let θ_Vi = θ_i id_Vi
> for some θ_i ∈ k. Since θ_1 = id_1, θ_0 = 1.

**Section 4.1, pages 21--22, (4.1) and (4.3).**

> s = ρ(s) and t = ρ(t). Then (4.1) s = ζ^3/(x^3 p+_A) s~, t = (x/ζ) t~ ∈ GL_Π(Q_n).

> Following [dBG, App. B], [CG1] or [ENO, App.], for each σ ∈ Aut(Q_ab), there exists a unique
> permutation, denoted by sigma^, on Π such that (4.2) σ(s_ij/s_0j) = s_(i sigma^(j))/s_(0 sigma^(j)) for all
> i, j ∈ Π. Moreover, there exists a function eps_sigma : Π → {±1} such that (4.3) σ(s_ij) =
> eps_sigma(i) s_(sigma^(i) j) = eps_sigma(j) s_(i sigma^(j)) for all i, j ∈ Π.

**Proposition 4.7, page 26.**

> Suppose A is a modular category over k with Frobenius-Schur exponent N and T-matrix
> t~ = [δ_ij θ_i]_(i,j∈Π_A), and let ζ ∈ k be a 6-th root of the anomaly α = p+_A/p−_A of A. Then for any
> σ ∈ Aut(Q_ab) and i ∈ Π_A, (4.12) θ_(sigma^(i))/σ^2(θ_i) = θ_(sigma^(0)) = ζ/σ^2(ζ).

The target's items (DLN0), (DLN1) and (DLN2) are these three passages, taken with `k = C`. The ratio form
of (DLN2) divides (4.12) for `i` by (4.12) for `j`.

**Trust surface.**
- The proof of (4.12) goes through Theorem II (iii) of the source, which was not re-checked.
- The spherical structure is part of the data of `A`, and the twists `theta_i` are those of that structure.
