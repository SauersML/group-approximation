---
rg: 2
id: seward-rokhlin-entropy-subadditivity-citation
kind: route
title: Import Seward's countable sub-additivity of outer Rokhlin entropy from Krieger II
target: seward-rokhlin-entropy-subadditivity
requires: []
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

Citation import from B. Seward, arXiv:1501.03367v4. Read on 2026-09-12 from the PDF text already extracted on MSI (`review-lit/entropy/1501.03367.txt`, lines 405-482). Spacing lost in extraction is restored below.

- "we define the relative Rokhlin entropy of G y (X,µ) relative to F, denoted h^Rok_G(X,µ|F), as inf{H(α|F∨I_G) : α is a countable Borel partition and σ-alg_G(α)∨F∨I_G = B(X)}. Since we only work with ergodic actions here, I_G will always be trivial"
- "For a p.m.p. ergodic action G y (X,µ), a collection C of Borel sets, and a G-invariant sub-σ-algebra F, we define the outer Rokhlin entropy as h^Rok_(G,µ)(C|F) = inf{H(α|F) : α is a countable Borel partition and C ⊆ σ-alg_G(α)∨F}."
- "Corollary 2.5. Let G y (X,µ) be a p.m.p. ergodic action, let C ⊆ B(X), let Σ be a G-invariant sub-σ-algebra, and let (F_n)_(n∈N) be an increasing sequence of G-invariant sub-σ-algebras with C ⊆ ∨_(n∈N) F_n ∨ Σ. Then (2.1) h^Rok_(G,µ)(C|Σ) ≤ h^Rok_(G,µ)(F_1|Σ) + Σ_(n≥2) h^Rok_(G,µ)(F_n|F_(n−1)∨Σ)."

The same specialization was checked independently in `research/artifacts/review-rokhlin-self-copy-dichotomy-2026-09-12.md`, item (a). Nothing is re-proved here; the trust surface is Seward's paper.
