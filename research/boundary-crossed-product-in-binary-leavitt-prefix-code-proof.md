---
rg: 2
id: boundary-crossed-product-in-binary-leavitt-prefix-code-proof
kind: route
title: Second route - code ∂F_d by complete prefix codes and send the generators to Thompson V units, with injectivity from simplicity and no graph-algebra or Brownlowe–Sørensen input
target: boundary-crossed-product-embeds-unitally-in-binary-leavitt
requires: []
artifacts:
  - research/artifacts/sk-hyperlinear-boundary-b-2026-09-13-part1.md
---

A direct proof. It is independent of `boundary-crossed-product-embeds-unitally-in-binary-leavitt-proof`, which
composes `boundary-crossed-product-is-a-leavitt-path-algebra` with the Brownlowe–Sørensen import; this route uses
neither. Details and a worked `d = 2` instance are in the artifact, §1.

**Notation.**
- `L = L_k(1,2) = k<s_1,s_2,t_1,t_2 | t_i s_j = δ_ij, s_1t_1 + s_2t_2 = 1>`, over any field `k`.
- For a binary word `w = w_1⋯w_n`, put `s_w = s_(w_1)⋯s_(w_n)` and `t_w = t_(w_n)⋯t_(w_1)`.
- Three facts:
  - (W1) `t_w s_w = 1`.
  - (W2) `t_w s_v = 0` when neither of `w, v` is a prefix of the other, and `t_w s_(wv) = s_v`.
  - (W3) `Σ_(w ∈ Q) s_w t_w = 1` for every complete prefix code `Q`.
- `R_∂ = LC(∂F_d, k) ⋊ F_d` with `u_g P_U u_g^(-1) = P_(gU)`. The letters are `Σ = {c_i^(±1)}` (`2d` of them), and
  `C(w)` is the cylinder of reduced words beginning with `w`.

**Step 1 (coding).**
- Fix a complete prefix code `{μ_x : x ∈ Σ}` with `2d` leaves.
- For each `x ∈ Σ`, fix a complete prefix code `{ν_(x,y) : y ≠ x^(-1)}` with `2d−1` leaves.
- Put `h(x_1x_2x_3⋯) = μ_(x_1) ν_(x_1,x_2) ν_(x_2,x_3) ⋯`.

Decoding leaf by leaf inverts `h`, so `h : ∂F_d -> {1,2}^N` is a homeomorphism. It maps `C(x_1⋯x_n)` onto the
binary cylinder `[μ_(x_1)ν_(x_1,x_2)⋯ν_(x_(n−1),x_n)]`.

**Step 2 (diagonal).** `[β] ↦ s_β t_β` is a unital ring homomorphism `LC({1,2}^N, k) -> L`.
- By (W3), `s_β t_β = s_(β1)t_(β1) + s_(β2)t_(β2)`.
- By (W1)–(W2), `s_β t_β s_γ t_γ` equals `s_γ t_γ` or `0` according as `β` is a prefix of `γ` or incomparable with
  it.

Put `Ψ_0(f) = image of f∘h^(-1)`.

**Step 3 (units).**
- For complete prefix codes `D, E` and a bijection `φ : D -> E`, let `U_φ = Σ_(w ∈ D) s_(φ(w)) t_w`.
  - It is a unit with inverse `Σ_w s_w t_(φ(w))`.
  - `U_φ χ_A U_φ^(-1) = χ_(φ^(A))`, where `φ^` replaces a prefix `w ∈ D` by `φ(w)`. This follows from
    `U_φ s_(wv) = s_(φ(w)v)`, by (W2).
- For a letter `c`, take the complete codes `D_c = {μ_x : x ≠ c^(-1)} ∪ {μ_(c^(-1))ν_(c^(-1),y) : y ≠ c}` and
  `E_c = {μ_cν_(c,x) : x ≠ c^(-1)} ∪ {μ_y : y ≠ c}`.
  - Let `φ_c(μ_x) = μ_cν_(c,x)` and `φ_c(μ_(c^(-1))ν_(c^(-1),y)) = μ_y`.
  - Then `φ_c^ = h∘c∘h^(-1)`. If `x_1 ≠ c^(-1)`, then `cξ = c x_1 x_2 ⋯`. If `ξ = c^(-1) y ⋯`, then `cξ = y ⋯`.
- Since `F_d` is free, `c_i ↦ U_(φ_(c_i))` extends to a homomorphism `g ↦ U_g`. By induction on word length,
  `U_g Ψ_0(P_U) U_g^(-1) = Ψ_0(P_(gU))`.

**Step 4 (homomorphism).** `R_∂` is free as a left `LC(∂F_d,k)`-module on `{u_g}`. So
`Ψ(Σ_g f_g u_g) = Σ_g Ψ_0(f_g) U_g` is well defined, multiplicative by Step 3, and unital.

**Step 5 (injectivity).** `R_∂` is simple, so `Ψ` is injective.
- **Minimality.** Given `ξ` and `C(w)`, choose a letter `a ∉ {w_n^(-1), ξ_1^(-1)}`. Then `waξ ∈ C(w)`.
- **Topological freeness.** `Fix(g)` has at most two points for `g ≠ 1`.
- **Every nonzero ideal `I` is all of `R_∂`.**
  - `I` contains some `r = Σ f_g u_g` with `f_1 ≠ 0`. Let `S` be the finite set of `g ≠ 1` with `f_g ≠ 0`.
  - Pick `x` with `f_1(x) = λ ≠ 0` and `gx ≠ x` for all `g ∈ S`. Take a clopen `V ∋ x` on which `f_1 = λ` and with
    `gV ∩ V = ∅` for `g ∈ S`.
  - Then `P_V r P_V = λP_V`, so `P_V ∈ I`.
  - By minimality and compactness, finitely many translates `g_jV` cover `∂F_d`. So
    `1 = 1 − Π_j(1 − u_(g_j)P_V u_(g_j)^(-1)) ∈ I`.
- A unital ring homomorphism out of a simple ring is injective.

**Credit.** No novelty.
- C*-setting: Spielberg's identification of `C(∂F_d) ⋊ F_d` with a Cuntz–Krieger algebra.
- Algebraic setting: Brownlowe–Sørensen.
- Simplicity: Clark–Edie-Michell and Steinberg (`steinberg-algebra-simple-iff-minimal-effective`).
- What this route adds is an explicit form: `F_d` sits inside Thompson's `V ⊂ L_k(1,2)^x` with the boundary action,
  and there is no graph identification.
