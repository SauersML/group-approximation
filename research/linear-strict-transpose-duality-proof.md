---
rg: 2
id: linear-strict-transpose-duality-proof
kind: route
title: Read configurations as the algebraic dual of finite support and transpose the automaton
target: linear-strict-pairs-are-transposes-of-post-surjective-automata
requires: []
artifacts:
  - research/artifacts/ideas-gottschalk-2-2026-09-14.md
---

Notation is as in the target claim. Write `Φ = k[G]^n` for the finitely
supported configurations, and `e_i` for the standard basis row vectors.

**Step 1: pairing.**
- Put `<x, f> = Σ_g x(g) f(g)^T` for `x` in `X` and `f` in `Φ`. The sum is
  finite.
- Every linear functional on `Φ` is determined by its values on the basis
  `e_i δ_g`. So `x -> <x, ->` identifies `X` with the algebraic dual `Φ^*`.

**Step 2: τ is the adjoint of τ^T on finite support.**
- `τ^T` maps `Φ` into `Φ`. Put `ψ = τ^T|_Φ`.
- For `x` in `X` and `f` in `Φ`, substitute `h = gm`:
  `<τ(x), f> = Σ_g Σ_m x(gm) A_m f(g)^T = Σ_h x(h) (Σ_m f(h m^(-1)) A_m^T)^T = <x, ψ(f)>`.
- So `τ = ψ^*` under Step 1.

**Step 3: linear duality.**
- For a linear map `ψ : Φ -> Φ`:
  - `ψ^*` is injective iff `ψ` is surjective;
  - `ψ^*` is surjective iff `ψ` is injective.
- **Proofs.**
  - If `ψ` is surjective, `ψ^*(x) = 0` makes `x` vanish on `ψ(Φ) = Φ`.
  - If `ψ` is not surjective, extend a basis of `ψ(Φ)` to one of `Φ`. This
    gives a nonzero functional vanishing on the image, and it lies in the
    kernel of `ψ^*`.
  - If `ψ` is injective, a functional `y` on `Φ` transports to `ψ(Φ)` by
    `y∘ψ^(-1)`. Extend it to `x` on `Φ`; then `ψ^*(x) = y`.
  - If `ψ(f_0) = 0` with `f_0 != 0`, every `ψ^*(x)` vanishes at `f_0`, while
    some functional does not.

**Step 4: finite-support readings of the dual properties.**
- `τ^T` is linear and maps `Φ` into `Φ`.
- **Pre-injectivity.** It means `τ^T(d) != 0` for every nonzero `d` in `Φ`,
  taking `d = x - x'`. That is, `ψ` is injective.
- **Post-surjectivity.** It means `ψ` is surjective.
  - If `ψ` is surjective and `y' - τ^T(x) = d` lies in `Φ`, pick `c` in `Φ` with
    `ψ(c) = d` and put `x' = x + c`.
  - Conversely, take `x = 0` and `y' = d` in `Φ`.

**Step 5: assemble (1).**
- By Steps 2 and 3, `τ` is injective and not surjective iff `ψ` is surjective
  and not injective.
- By Step 4, that holds iff `τ^T` is post-surjective and not pre-injective.

**Step 6: the matrix form, (2) and (3).**
- `ψ` commutes with left translation. Identify `f` with `Σ_h f(h) h` in
  `k[G]^n`. Then `ψ(f) = f c` with `c = Σ_m A_m^T m`, because
  `ψ(e_i) = Σ_m e_i A_m^T m`.
- **If `ψ` is surjective and not injective.** Choose rows `d_i` with
  `d_i c = e_i`, so `dc = I_n`. If `cd = I_n`, then `fc = 0` gives
  `f = f c d = 0`, contradicting non-injectivity. So `cd != I_n`.
- **Conversely, if `dc = I_n != cd`.**
  - `ψ` is surjective, since `f = (f d) c`.
  - `E = I_n - cd` is nonzero with `E c = c - c d c = 0`, so a nonzero row of
    `E` lies in the kernel.
- Every `c` in `M_n(k[G])` arises from some finite `M` and matrices `A_m`. This
  gives (3).
- In characteristic zero, `M_n(k[G])` is directly finite for every group
  (Kaplansky), so no witness exists there.
