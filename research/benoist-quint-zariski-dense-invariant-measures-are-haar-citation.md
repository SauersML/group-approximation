---
rg: 2
id: benoist-quint-zariski-dense-invariant-measures-are-haar-citation
kind: route
title: Benoist-Quint 2011, Corollaire 1.2, read verbatim from the preprint PDF
target: benoist-quint-zariski-dense-invariant-measures-are-haar
requires: []
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-microstates-2026-09-13.md
---

Y. Benoist, J.-F. Quint, *Mesures stationnaires et fermés invariants des espaces homogènes*, Ann. of Math.
174 (2011). Read from the preprint `prepubli/09stationnaire.pdf` on Benoist's homepage, page 2:

> **Corollaire 1.2.** Soient G un groupe de Lie réel quasi-simple connexe, Λ un réseau de G, X = G/Λ et
> Γ un sous-semi-groupe Zariski dense de G. Alors,
> a) Toute probabilité Γ-invariante sans atome ν sur X est la probabilité de Haar.
> b) Tout fermé Γ-invariant infini F de X est égal à X.
> c) Tout suite de Γ-orbites finies distinctes X_n dans X s'équirépartit vers la probabilité de Haar.

Conventions (pages 1--2): *"Un groupe de Lie réel G est dit quasi-simple si son algèbre de Lie est
simple"*. A measure is atom-free (*sans atome*) when `ν({x}) = 0` for every `x`. For non-linear `G`,
Zariski dense means that `Ad(Γ)` is Zariski dense in `Ad(G)`.

The page-2 statement was checked against the preprint, not the journal version. The corollary follows
from Théorème 1.1 of the same paper, which treats atom-free `μ`-stationary measures for compactly
supported `μ` whose support generates a Zariski-dense sub-semigroup.
