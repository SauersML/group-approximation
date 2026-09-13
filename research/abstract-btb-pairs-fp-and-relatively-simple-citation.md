---
rg: 2
id: abstract-btb-pairs-fp-and-relatively-simple-citation
kind: route
title: Import FFWZ Theorem 3.6, Theorem 4.1(ii) and Lemma 5.2
target: abstract-btb-pairs-fp-and-relatively-simple
requires: []
---

This imports three results of Fournier-Facio--Wu--Zaremsky, *Abstract twisted
Brin--Thompson groups*, arXiv:2603.24687v2. They were read on 2026-09-12 from the
PDF text extracted on MSI, `/scratch.global/sauer354/bh-reviewer/2603.24687.txt`.
- **Theorem 3.6 (Theorem A), lines 667–670:** "Let G be a group acting on a
  non-empty set S. The abstract twisted Brin–Thompson group SV_G is relatively
  simple, with largest normal subgroup the canonical kernel SK_G."
- **Theorem 4.1(ii) (Theorem B), lines 107–111 and 750:** SV_G "is finitely
  presented if and only if G ↷ S is of type [A_2]".
- **Lemma 5.2, lines 1204–1210:** "Let G ↷ S be a group action with kernel K.
  Then the normal pair (G,K) sharply embeds in SV_G." The proof sends g to
  [·,id,g,·] and checks that [·,id,g,·] ∈ SK_G forces g ∈ K.

The canonical kernel is their Definition 2.12 (lines 502–511). Relative simplicity
is Definition 1.2 (lines 56–60), and type [A_n] is defined at lines 84–91. The
statements were read in full; the proofs of Theorems 3.6 and 4.1 were not
re-checked line by line.
