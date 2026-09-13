---
rg: 2
id: radu-lattice-one-sided-pairs-need-residual-coincidences
kind: claim
title: A one-sided inverse pair over Radu's lattice is two-sided modulo the finite residual, so its supports have total radius at least four
distinct_from:
  one-sided-inverse-pairs-transfer-to-table-realizations: that pushes a pair forward along any map multiplicative on the supports; this applies it to the residually finite quotient of one explicit lattice and bounds the supports by the length of the shortest element of its finite residual.
  radu-bmw-coordinate-subgroups-are-sofic: that screens supports through subgroups containing all horizontal or all vertical letters; this classifies every set of letters and forces two defect points into one coset of the finite residual.
  radu-lattice-defect-idempotents-avoid-finite-subgroups: that keeps the defect out of finite-subgroup algebras; this places two points of the defect support in one coset of the finite residual.
artifacts:
  - research/artifacts/radu-lattice-anchored-linear-gadgets-2026-09-12.md
---

**ESTABLISHED** by `radu-lattice-residual-coincidences-proof`.

Let `Gamma_R` be Radu's BMW lattice (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), `Gamma_0` its
finite residual, and `B_r` the ball of radius `r` in the six letters. Let
`A, B in M_n(F_p[Gamma_R])` with `B A = I_n`, and let `S_A`, `S_B` be the unions of the entry supports.

**Theorem.**
1. **Residual coincidence.** Modulo `Gamma_0`, `A B = I_n`. So each entry of `I_n - A B` has
   coefficient sum zero on every coset of `Gamma_0`. If `A B != I_n`, then `S_A S_B ∪ {1}` contains
   `g != h` with `g^(-1) h in Gamma_0`.
2. **Radius.** `delta^(+-4) = (xz)^(+-4)` are the shortest elements of `Gamma_0` (Remark 3.6, imported
   by `radu-bmw-lattice-embeds-in-titz-witzel-kernel`). So `S_A ⊆ B_r`, `S_B ⊆ B_s` and `A B != I_n`
   force `r + s >= 4`. Length alone gives nothing more: `(zx)^2` and `(xz)^2` lie in `B_4`, and
   `((zx)^2)^(-1) (xz)^2 = delta^4`.
3. **Unit ball, size one.** If `n = 1` and `S_A ∪ S_B ⊆ B_1`, then `A B = 1` over every commutative
   coefficient ring. Over `F_2` the solutions of `B A = 1` are `A = B` in `{1, h, v, 1 + h + v}`,
   with `hv = vh` in the last case.
4. **Letter sets.** A set of letters generates `Gamma_R` iff it contains `{a,y,z}`, `{b,x,y}`,
   `{b,y,z}`, `{c,x,y}` or `{c,y,z}`. Otherwise it generates a sofic subgroup.

**Screen for automata.** For a strict pair of automata on `Gamma_R`, quotient folding
(`strict-pairs-transfer-to-table-realizations`, Corollary 2) gives the nonlinear form of item 1.
Every Garden of Eden window distinguishes two cells whose difference lies in `Gamma_0 \ {1}`, so by
item 2 it has diameter at least eight.

Proof: Sections 1--3 and 5 of the artifact.
