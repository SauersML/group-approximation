---
rg: 2
id: jeandel-rao-substitutive-structure-citation
kind: route
title: Labbé, Substitutive structure of Jeandel-Rao aperiodic tilings (arXiv:1808.07768v4, DCG 65 (2021) 800-855), and Labbé-Mann-McLoud-Mann, Nonexpansive directions in the Jeandel-Rao Wang shift (arXiv:2206.02414v3, DCDS 43 (2023) 3213-3250), read as PDFs
target: jeandel-rao-minimal-subshift-is-morphic-image-of-labbe-shift
requires: []
---

The PDFs were read page by page on 2026-09-18 (lane bh-g2-abh). Printed page numbers are cited, and all
quotations are short.

## [L] S. Labbé, *Substitutive structure of Jeandel–Rao aperiodic tilings*, arXiv:1808.07768v4, 18 Dec 2019

Published as Discrete Comput. Geom. 65(3) (2021) 800–855.

- **p. 2, Theorem 1.** There is an aperiodic minimal subshift `X_0` of `Ω_0` such that any tiling in it
  "can be decomposed uniquely into 19 distinct patches". These patches are equivalent to `U`.
- **p. 3, Figure 3.** The diagram `X_0 ← X_1 ← X_2 ← X_3 ← X_4 ← Ω_5 ← Ω_6 ← … ← Ω_12 ← Ω_U`. The
  arrows are `ω_0, …, ω_3, ȷ, η, ω_6, …, ω_11, ρ`.
- **p. 4.** "each morphism `ω_i` with `0 ≤ i ≤ 3` or `6 ≤ i ≤ 11` is recognizable and onto up to a
  shift". Also, `ȷ` and `η` are one-to-one and onto (`ȷ` onto its image `X_4`).
- **p. 5, Theorem 3, items (i)–(v).**
  - (i) and (iv): recognizable morphisms, onto up to a shift (`\overline{ω_i(Ω_(i+1))}^σ = Ω_i`).
  - (ii): `ȷ: Ω_5 → Ω_4` is "a topological conjugacy onto its image".
  - (iii): `η: Ω_6 → Ω_5` is a shear conjugacy for `(1 1; 0 1)`.
  - (v): "`Ω_12` is equivalent to `Ω_U`".
- **p. 5, Corollary 5**, with the definitions of `X_4, …, X_0` given just before it.
- **p. 6, §2.1.** Definitions of conjugacy and `GL_d(Z)`-conjugacy (`σ^(Mk) ∘ θ = θ ∘ σ^k`); a shear
  conjugacy is the case of a shear matrix `M`.
- **p. 7, §2.2.** Equivalence of tile sets is by bijections of the colour sets.
- **pp. 10–11, §2.7.** A 2-dimensional morphism satisfies `ω(u ⊙^i v) = ω(u) ⊙^i ω(v)`. The notation
  `\overline{X}^σ = ∪_k σ^k X` is fixed on p. 5.
- **p. 12, §2.9.**
  - An `ω`-representation of `y` is a pair `(k, x)` with `y = σ^k ω(x)`.
  - It is *centered* if `0 <= k < shape(ω(x_0))`.
  - `ω` is recognizable in `X` if each `y` has at most one centered representation.
- **pp. 16–17, Theorem 16 and Algorithm 2.** Marker desubstitutions have letter images in
  `(T∖M) ∪ ((T∖M) ⊙^i M)`, respectively `(T∖M) ∪ (M ⊙^i (T∖M))`: single tiles or dominoes.

## [LMM] S. Labbé, C. Mann, J. McLoud-Mann, *Nonexpansive directions in the Jeandel–Rao Wang shift*, arXiv:2206.02414v3, 29 Apr 2023

Published as Discrete Contin. Dyn. Syst. 43 (2023) 3213–3250.

- **p. 4.**
  - "The description of the minimal subshift `X_0` was given as a subshift of finite type in [Lab21c]",
    where [Lab21c] is [L].
  - `X_0` is also given as the symbolic system of a toral `Z^2`-rotation coded by a polygonal partition.
  - **Theorem A:** `X_0` "contains exactly 4 nonexpansive directions", with slopes
    `{0, φ+3, −3φ+2, −φ+5/2}`.
- **pp. 11–12.** `Γ_0 = ⟨(φ,0), (1, φ+3)⟩` and `R_0^n(x) = x + n`. **Theorem 4.1:** `X_(P_0,R_0) ⊊ Ω_0` is
  proper, minimal and aperiodic, and `R_0` is its maximal equicontinuous factor.
- **p. 29.** The reference list identifies [Lab21c] as [L].

## [ABHT] arXiv:2204.11492v3

TeX copy at `$GQ/src/bh-g2-fixedpoint-b/abht-main.tex`.

- **ll. 520–522, Theorem `theorem:SFT_Labbe`.** The theorem cites [LMM] and Labbé's two 2021 papers for
  "an aperiodic, minimal SFT `X_0`" with the same four slopes.
- **ll. 524–554.** ABHT pass to a conjugate vertically expansive Wang tile SFT with thickening 0, then
  rotate it by `π/2`.

## Not checked

- The 12 elementary steps of [L] were not re-verified. They are computer-assisted (SageMath, with a
  Jupyter notebook cited in [L]).
- The DCG print version was not compared with arXiv v4.
