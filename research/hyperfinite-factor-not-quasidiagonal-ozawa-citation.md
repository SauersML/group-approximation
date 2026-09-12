---
rg: 2
id: hyperfinite-factor-not-quasidiagonal-ozawa-citation
kind: route
title: Import Ozawa's MF algebra whose spatial tensor product with R is infinite
target: hyperfinite-factor-not-quasidiagonal
requires: []
artifacts:
  - research/artifacts/ozawa-r-not-quasidiagonal-import-2026-09-12.md
---

Literature import. N. Ozawa, "The hyperfinite II1 factor is not
quasidiagonal", arXiv:2609.08892v1 (submitted 2026-09-08; the PDF footer
is dated September 9, 2026). It was read from the PDF on 2026-09-12.
Theorem (p. 1): "There is a unital separable MF C*-algebra A such that
the spatial tensor product A ⊗ R of A and the hyperfinite II1 factor R is
infinite. Consequently, stable finiteness of C*-algebras is not stable
under tensor product and the hyperfinite II1 factor is not a
quasidiagonal C*-algebra."

The paper's definition for a non-separable algebra is that R "is
quasidiagonal if every separable C*-subalgebra of it is quasidiagonal"
(p. 1). That is the sense of the target claim. The step from the
infinite tensor product to non-quasidiagonality of R is cited there to
Lemma 4 of Goldbring--Sinclair, Internat. J. Math. 28 (2017) 1750008;
this import did not re-read that lemma. The preprint is v1 only and has
not been refereed. The author states that the result was obtained using
OpenAI's Chat GPT Pro 6.0.

This import is now the derivation of record for the target. The group
witness route `hyperfinite-factor-not-qd-via-non-mf-unitary-subgroup`
stays open and is no longer needed. The artifact lists what the paper
does not settle: Kaplansky's quasitrace problem, Problem VII, the exact
residual of X(1), and MF-ness of R.
