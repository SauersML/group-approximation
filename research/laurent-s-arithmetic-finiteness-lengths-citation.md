---
rg: 2
id: laurent-s-arithmetic-finiteness-lengths-citation
kind: route
title: Bux--Gramlich--Witzel Rank Theorem with Behr's finite generation and presentation criteria
target: laurent-s-arithmetic-finiteness-lengths
requires: []
---

Source: K.-U. Bux, R. Gramlich, S. Witzel, *Higher finiteness properties of
reductive arithmetic groups in positive characteristic: the Rank Theorem*,
arXiv:1102.0428v1 (30 January 2011), pages 1–2.  Read from the arXiv PDF on
2026-09-13 (downloaded on MSI, pages rendered and read directly).

Verbatim, page 2:

> **Rank Theorem.** Let 𝒢 be a connected non-commutative absolutely almost
> simple K-isotropic K-group. Then the finiteness length φ(Γ) of the
> S-arithmetic group Γ = 𝒢(𝒪_S) is d − 1 where d := Σ_{p∈S} dim(X_p) is the
> sum of the local ranks of 𝒢.

Verbatim, page 2, on the earlier criteria:

> In 1969, H. Behr [Behr69] proved that Γ is finitely generated if and only
> if d > 1. [...] Using Harder's reduction theory again, Behr [Behr98]
> showed in 1998 that Γ is finitely presented if and only if d > 2.

and

> Interest in finiteness properties of Γ started in 1959 when H. Nagao
> [Naga59] showed that SL₂(𝔽_q[t]) is not finitely generated. In this case,
> there is a single place and the corresponding euclidean building is a
> tree, thus d = 1.

Page 1 defines type `F_m` (classifying space with finite `m`-skeleton) and
the finiteness length `φ(G)` as the largest `m` with `G` of type `F_m`.  So
type `F_1` is finite generation and type `F_2` is finite presentation.

Application.  `SL_n` is connected, non-commutative, absolutely almost simple
and split, hence `K`-isotropic.  Its local rank at every place is `n-1`,
the dimension of the Bruhat--Tits building.  For `K = F_q(t)`, the ring of
functions regular away from `{t=0, t=infinity}` is `F_q[t,1/t]`, and the ring
of functions regular away from `{t=infinity}` is `F_q[t]`.  So `d = 2(n-1)` in
the Laurent case and `d = n-1` in the polynomial case, which gives the
table in the claim.
