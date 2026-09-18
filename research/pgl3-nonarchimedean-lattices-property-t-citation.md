---
rg: 2
id: pgl3-nonarchimedean-lattices-property-t-citation
kind: route
title: Import Bekka--de la Harpe--Valette Theorems 1.3.4, 1.4.15 and 1.7.1 for lattices in PGL_3 over a local field
target: pgl3-nonarchimedean-lattices-have-property-t
requires: []
---

**Source.** B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, New
Mathematical Monographs 11, Cambridge University Press 2008.

**How it was read.** Read on 2026-09-17 from the authors' preprint PDF dated February
23, 2007 (title page: "Kazhdan's Property (T) / B. Bekka, P. de la Harpe and A.
Valette / February 23, 2007"). The PDF was fetched from
`https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf` and extracted with
pdfminer. Book chapter 1 matches the Cambridge numbering already used in
`bdhv-central-extension-property-t-citation`.

**Verbatim.**

- Section 1.3 (Compact generation and other consequences):
  > Theorem 1.3.4 Let G1 and G2 be topological groups, and let ϕ : G1 → G2 be a
  > continuous homomorphism with dense image. If G1 has Property (T), then G2 has
  > Property (T).
- Section 1.4 (Property (T) for SLn(K), n ≥ 3):
  > Theorem 1.4.15 Let K be a local field. The group SLn(K) has Property (T) for any
  > integer n ≥ 3.
- Section 1.7 (Hereditary properties), "Property (T) is inherited by lattices":
  > Theorem 1.7.1 Let G be a locally compact group, and let H be a closed subgroup of G
  > such that G/H has a finite invariant regular Borel measure. The following are
  > equivalent:
  > (i) G has Property (T);
  > (ii) H has Property (T).
  > In particular, if Γ is a lattice in G, then Γ has Property (T) if and only if G has
  > Property (T).

**Hypothesis match.**
- `K` is a nonarchimedean local field, so it is a local field and Theorem 1.4.15
  applies with `n = 3`.
- Theorem 1.3.4 is applied to `SL_3(K) -> H`, which is continuous and onto.
- Theorem 1.7.1 is applied twice:
  - to the open finite-index subgroup `H ≤ PGL_3(K)` with counting measure on
    `G/H`;
  - to the lattice `Γ`.
- The elementary facts about `K^*/(K^*)^3` are proved in the claim and are not imported.
