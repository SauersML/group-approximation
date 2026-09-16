---
rg: 2
id: pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3-proof
kind: route
title: "Meier–Meinert–VanWyk on the curve complex of the punctured disk, with central Dehn twists in every cell stabilizer"
target: pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3
requires: []
artifacts:
  - research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md
---

Complete proof in the artifact, Sections 1 to 3 (Lemmas 1 to 5 and Theorem M).

- Tools, quoted verbatim from Zaremsky arXiv:1803.02717: (T1) Meier–Meinert–VanWyk
  Theorem 2.4 (cocompact action on an `(m-1)`-connected complex, with nontrivial
  restrictions to cell stabilizers and stabilizer levels `m - dim sigma`), and
  (T2) MMV Theorem 2.1 (nonzero on the center gives `Sigma^m` for type `F_m`).
- `P_n` acts on the curve complex `C(D_n) = C(S_{0,n+1})`, which is
  `(n-4)`-connected. This is Harer's theorem, taken from Davis–Huang
  arXiv:2003.13553v2, Theorem 5.12 and the type `A_{n-1}` remark.
- Lemma 1: pure classes preserve the puncture set inside a curve, and the types
  of a multicurve are distinct and laminar. So a simplex stabilizer fixes each
  curve.
- Lemma 2: for `c` in `sigma`, `T_c` is central in `Stab(sigma)` and
  `chi(T_c) = c_{A(c)}` (change of coordinates plus forgetting strands).
- Lemma 3: finitely many orbits of simplices, via laminar families of types.
- Lemma 4: stabilizers have type `F`, by the cutting homomorphism onto products
  of `PMod(S_{0,k})`, with a free abelian kernel and a central extension by
  `<T_∂>`.
- Proof: every cell stabilizer contains a central twist with a nonzero value, so
  (T2) gives `Sigma^infinity` for every restriction, and (T1) with
  `m = n - 3` gives `[chi]` in `Sigma^{n-3}(P_n)`.

Standard mapping class group facts (change of coordinates, `f T_c f^{-1} = T_{f(c)}`,
the cutting homomorphism; Farb–Margalit) are used without re-reading.
