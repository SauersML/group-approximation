---
rg: 2
id: based-dehn-nielsen-baer-citation
kind: route
title: Import the based Dehn--Nielsen--Baer isomorphism and trivial center from the Farb--Margalit primer
target: based-dehn-nielsen-baer-for-closed-surfaces
requires: []
artifacts:
  - research/artifacts/solve-bh-3manifold-2026-09-13.md
---

Citation import. Source: B. Farb, D. Margalit, *A primer on mapping class
groups* (PDF fetched on MSI on 2026-09-13, text extracted locally with
`pdftotext`).

1. **Trivial center.** Section 1, displayed fact: "If S admits a hyperbolic
   metric, then the centralizer of any non-trivial element of π1(S) is cyclic.
   In particular, π1(S) has a trivial center." The argument follows it in the
   text.
2. **Based Dehn--Nielsen--Baer.** Section 8.2, "Once-punctured versus closed":
   "The Dehn–Nielsen–Baer theorem can be used to relate the group Mod(Sg) to
   the group Mod(Sg,1), where Sg,1 is the genus g ≥ 2 surface with one marked
   point." After an isomorphism of exact sequences from
   `1 → Inn(π1(Sg)) → Aut(π1(Sg)) → Out(π1(Sg)) → 1` to
   `1 → π1(Sg) → Mod±(Sg,1) → Mod±(Sg) → 1`, the text concludes: "The five
   lemma then tells us that the middle vertical map is an isomorphism from
   Mod±(Sg,1) to Aut(π1(Sg))."

Belk--Fournier-Facio--Hyde--Zaremsky use the same identification in the proof
of their Corollary B (arXiv:2503.21882v2, extracted text l.636--637):
"Identifying MCG(Σ∗) with Aut(π1(Σ)) via the Dehn–Nielsen–Baer Theorem [FM12,
Theorem 8.8]".
