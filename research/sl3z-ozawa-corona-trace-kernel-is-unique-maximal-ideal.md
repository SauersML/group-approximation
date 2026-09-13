---
rg: 2
id: sl3z-ozawa-corona-trace-kernel-is-unique-maximal-ideal
kind: claim
title: Every proper ideal of Ozawa's SL(3,Z) block corona lies in its trace kernel, which therefore has no unital quotient
distinct_from:
  sl3z-ozawa-block-corona-has-unique-trace: that computes the traces of the corona and shows the trace kernel is nonzero; this computes the maximal ideals of the corona, where the input is Boutonnet–Houdayer's weak containment of the regular representation in weakly mixing representations.
  sl3z-ozawa-corona-trace-kernel-is-stable: that asks whether the trace kernel is stable; this proves the ideal-theoretic necessary condition (no nonzero unital quotient) unconditionally, and leaves stability open.
artifacts:
  - research/artifacts/quasitrace-kernel-maximal-ideal-property-s-2026-09-12.md
---

**ESTABLISHED (derivation `sl3z-ozawa-corona-kernel-unique-maximal-ideal-proof`).**
Notation as in `sl3z-ozawa-block-corona-has-unique-trace`: `A = B/I`, and
`K = ker(q : A → C*_r(SL(3,Z)))` is the trace kernel.

**Statement.**
1. Every proper closed ideal of `A` is contained in `K`. So `K` is the unique maximal
   ideal of `A`, and `q` factors through every nonzero quotient of `A`.
2. `K` is an essential ideal of `A`.
3. `K` has no nonzero unital quotient.

**Why it matters.**
- A nonzero stable C*-algebra has no nonzero unital quotient, so item 3 is a
  necessary condition for `sl3z-ozawa-corona-trace-kernel-is-stable`, and it now holds.
- By Ortega–Perera–Rørdam, Proposition 4.5, item 3 makes "`K` has property (S)"
  equivalent to "`K` admits no nonzero bounded 2-quasitrace". That is the intrinsic
  form of the invisibility condition in
  `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`; see
  `sl3z-ozawa-corona-trace-kernel-has-property-s`.

**Imports, not re-derived:**
- Boutonnet–Houdayer, *Stationary characters on lattices of semisimple Lie groups*,
  arXiv:1908.07812v2, Corollary D, read from the PDF (pages 1–5) on 2026-09-12.
  - Hypotheses: `G` connected semisimple with trivial centre and no compact factor,
    all of whose simple factors have real rank at least 2; `Γ < G` an irreducible
    lattice; `π` weakly mixing.
  - Conclusions: `λ_Γ ≺ π`, and `ker(C*_π(Γ) → C*_λ(Γ))` is the unique proper maximal
    ideal of `C*_π(Γ)`.
  - These hypotheses cover `SL(3,Z) < SL(3,R)`.
- `kazhdan-block-algebras-contain-their-block-ideal`: `A` has no finite-dimensional
  representation.

Proof: §1 of the artifact.
