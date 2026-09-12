---
rg: 2
id: seward-weak-containment-relative-entropy-citation
kind: route
title: Import Theorem 1.2 of Seward's Weak containment and Rokhlin entropy
target: seward-weak-containment-relative-entropy-equality
requires: []
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

Citation import from B. Seward, *Weak containment and Rokhlin entropy*, arXiv:1602.06680v2 (30 May 2017). The PDF was fetched on MSI on 2026-09-12 and its text extracted with pdftotext. Spacing lost in extraction is restored below.

- **Introduction, definition.** "Let G be a countable group, let G y (X,µ) be a (not necessarily free) p.m.p. action, and let I_G denote the σ-algebra of G-invariant sets. [...] If F is a G-invariant sub-σ-algebra, then the Rokhlin entropy of G y (X,µ) relative to F, denoted h_G(X,µ|F), is inf{H(α|F∨I_G) : α countable partition and σ-alg_G(α)∨F∨I_G = B(X)}."
- **Theorem 1.2.** "Let G be a countably infinite group, let G y (X,µ) be a free p.m.p. action, and let F be a G-invariant sub-σ-algebra. If G y (Y,ν) is a p.m.p. action which is weakly contained in all free p.m.p. actions of G then h_G(X,µ|F) = h_G(X×Y,µ×ν|F∨B(Y))."

The paper notes before the theorem that the direct-product equality `h_G(X × Y | B(Y)) = h_G(X)` "is known to hold when G is amenable but is unknown otherwise", and that Theorem 1.2 establishes it under the weak containment hypothesis. Nothing is re-proved here.
