---
rg: 2
id: kms-fp-rf-groups-with-arbitrarily-large-depth-citation
kind: route
title: Import Kharlampovich-Myasnikov-Sapir Theorem 4.19 on depth functions of finitely presented residually finite groups
target: kms-fp-rf-groups-with-arbitrarily-large-depth
requires: []
artifacts:
  - research/artifacts/sk-wp-host-2026-09-13.md
---

O. Kharlampovich, A. Myasnikov and M. Sapir, *Algorithmically complex residually finite groups*, arXiv:1204.6506v5;
published in Bull. Math. Sci. 7 (2017), 309–352.

Verbatim from the arXiv v5 source (`KMS-322.tex`, fetched and read on MSI, 2026-09-13), §4.4 "Residually finite
finitely presented group with large depth function", Theorem 4.19 in the PDF numbering:

> For every recursive function $f$ there exists a finitely presented residually finite group $G$ from
> ${\mathcal A}_p^2{\mathcal A}\cap {\mathcal Z}{\mathcal N}_3{\mathcal A}$ such that $\rho_G(n)>f(n)$ for all $n$.
> In addition, we can assume that the word problem in $G$ is as hard as the membership problem for any prescribed
> recursive set of natural numbers.

Definition (§1, "Quantification of the 'no' part: the depth function"), verbatim:

> the depth function $\rho_G(n)$ is the smallest function such that every two words $w\ne_G w'$ of length at most $n$
> are separated by a homomorphism to a group (semigroup) $H$ with $|H|\le \rho_G(n)$. That function does not depend on
> the choice of finite generating set $X$ (up to the natural equivalence).

The claim uses the depth function on one fixed finite generating set of `G`, the one in which `ρ_G(n) > f(n)` holds,
so the equivalence under change of generating set is not needed. The journal theorem number was not checked; the
arXiv v5 PDF prints it as Theorem 4.19, and main's time-complexity import cites that paper's Theorem 4.21.
