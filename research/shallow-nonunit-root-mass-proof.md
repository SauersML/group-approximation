---
rg: 2
id: shallow-nonunit-root-mass-proof
kind: route
title: Compressors collapse shallow characters to constant terms, and the Laurent torus kills the constant terms on an EL_2 ⋉ R^2 block
target: shallow-nonunit-root-mass-vanishes-under-vertex-rounding
requires:
  - compressor-transport-exactifies-under-vertex-rounding
  - elementary-linear-semidir-pair-relative-t
  - pure-nonunit-root-mass-is-log-scale-folner
artifacts:
  - research/artifacts/nh-shallow-torus-mass-2026-09-12.md
---

Full derivation in the artifact.

**Lemma D, the compressor (§1).**
- `φ_A(m) ⊆ z R_+` for `m = (x_1..x_d)`, since every coordinate of `Aa` is at least `|a|_1`.
- For `χ` trivial on `z R_+`, `χ ∘ φ_A = (χ|_1) ∘ ev_0`: the compressor collapses every shallow
  character to its constant-term character.
- Lemma A with the single-point test sets `{ψ_0}` gives
  `μ_n(shallow, restriction to constants ψ, χ ≠ ψ_0) <= η_n` for each `ψ`.
- Summing over the `q` values of `ψ` gives item 1.

**Lemma E, the torus (§2).**
- `t = diag(x_1, x_1, x_1^(-2), 1, ...) ∈ EL_r(L)` by Whitehead's lemma. It is the identity on the
  `EL_2(R_+)` block and multiplies `V = e_13(R_+) × e_23(R_+)` by `x_1^3`. So `π_n ∘ Ad t` is a
  genuine representation of `S = EL_2(R_+) ⋉ V`.
- The defect `δ_n^t -> 0`, because `σ` is a homomorphism and `(H1)` controls fixed words.
- `V` is normal in `S`, so the relative Kazhdan pair gives the linear inequality
  `||ξ - P^V ξ|| <= κ_S^(-1) max_(F_S) ||π(s)ξ - ξ||`.
- Apply it to `X -> π_n(Ad t(s)) X π_n(s)^*` at a unitary representative of `σ_n(t)`. This gives an
  exact intertwiner of `π_n|_V` and `π_n ∘ Ad t|_V` off trace `η_n^t`, hence
  `|μ_n^(13)(E) - μ_n^(13)(D_t^(-1)E)| <= η_n^t` with `D_t χ = χ(x_1^3 ·)`.
- A Weyl word transfers this from `e_13` to `e_12`.
- `D_t ψ_0 = 1` for every `ψ`, so `μ_n(E_0^*) <= η_n^t`. This is item 2.

**Items 3 and 4.** Add items 1 and 2, then add the log-scale Følner bound for depth above one.
