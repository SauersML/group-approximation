---
rg: 2
id: quantum-rigidity-passes-to-sub-sfts
kind: claim
title: Every subshift of finite type inside a quantum rigid SFT is quantum rigid, so its crossed-product algebra is finitely presented
distinct_from:
  permutive-triangle-sfts-are-quantum-rigid: that proves one class of SFTs rigid; this transfers rigidity from any rigid SFT to all of its sub-SFTs, turning the existence of a rigid free minimal SFT into an embedding question.
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that separates the first-order part of rigidity for one SFT; this compares local tiling algebras of an SFT and of its sub-SFTs.
artifacts:
  - research/artifacts/quantum-rigidity-group-shifts-and-gluing-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `X ⊆ A^(Z^2)` be an SFT that is `D`-quantum rigid, and let `Ω ⊆ X` be an
SFT with forbidden patterns in `B_(r')`. Put `D'' = max(D, r')`. Then `Ω` is `D''`-quantum rigid, and
`LC(Ω, k) ⋊ Z^2` is finitely presented (`sft-crossed-product-fp-iff-quantum-rigid`).

*Proof.* Take a `D''`-family `E` for `Ω`.
1. **Commutation.** It commutes at distance `<= 2D`, since `2D'' >= 2D`.
2. **Admissibility.** Let `π` be a `B_D`-pattern not occurring in `X`. The operators on `z + B_(D'')` commute,
   so summing over the extra sites gives `prod_(B_D) E_π = sum_(π') prod_(B_(D'')) E_(π')`, over the extensions
   `π'` of `π`. No `π'` occurs in `Ω ⊆ X`, so every term vanishes by (Q3) for `Ω`.
3. **Conclusion.** So `E` is a `D`-family for `X`, and it commutes. QED

**Corollaries.**
- **Unconditional.** Every sub-SFT of a triangle-permutive SFT is quantum rigid. Examples: Ledrappier's shift
  over any `F_p`, and matrix versions `x(z+e_2) = A x(z) + B x(z+e_1)` with `A, B` invertible. (Sub-SFTs of
  triangle-permutive SFTs are triangle-permutive anyway; the theorem is about arbitrary rigid ambients.)
- **Conditional.** If Bieri–Strebel is granted (`group-shift-crossed-product-fp-from-lamp-group-fp`), every
  sub-SFT of a group shift whose `Σ^c` has no antipodal pair is quantum rigid.
- **Reduction.** `free-minimal-z2-sft-is-quantum-rigid` holds iff some free minimal SFT embeds, as a sub-SFT, in
  some quantum rigid SFT. The natural unconditional ambients are the quasigroup spacetimes of
  `free-minimal-triangle-permutive-sft-exists`.

**Remark (heuristic, not checked).**
- **Group shifts.** If `Ω` is a sub-SFT of a group shift `X`, two points of `Ω` agreeing on a strip differ by an
  element of `X` vanishing there. So every nonexpansive direction of `Ω` is nonexpansive for `X`.
- **Labbé's shift.** Its irrational fault direction `(φ, 1)` should then keep it (and every recoding) out of
  group shifts whose nonexpansive set is rational (recalled for algebraic `Z^2`-actions).
- **Permutive SFTs.** The same should hold for triangle-permutive SFTs, whose nonexpansive directions should
  be the three sides.
