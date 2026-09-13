---
rg: 2
id: z2-o2-phantoms-are-not-square-zero
kind: claim
title: No nonzero Z/2-equivariant phantom has zero tensor square; on O_2, an outer action with contractible crossed product whose tensor square is Rokhlin is itself Rokhlin
distinct_from:
  zp-restriction-and-crossed-product-detect-kk-g-contractibility: that asks that every Z/2-phantom be zero; this asks only that no nonzero phantom be square-zero, which detection implies and which is what the Tate-diagonal reduction needs.
  z2-o2-phantom-tensor-square-is-sai-and-self-dual: that proves equivalent forms of square-zero-ness; this asks whether a square-zero phantom must be zero.
---

**OPEN.** `G = Z/2`.
- **Categorical form.** Let `D` be a separable `G`-algebra with `Res D ≃_KK 0` and `D ⋊ G ≃_KK 0`.
  If `D ⊗ D ≃_(KK^G) 0` (minimal tensor product, diagonal action), then `D ≃_(KK^G) 0`.
- **Nuclear dynamical form.** Let `α : G ↷ O_2` be pointwise outer with `O_2 ⋊_α G ≃_KK 0`. If
  `α ⊗ α` has the Rokhlin property, then so does `α`. By item 3 of
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, this is the categorical form for nuclear `D`.

**Relations.**
- Detection at `2` (`zp-restriction-and-crossed-product-detect-kk-g-contractibility`) implies this
  claim.
- By the square-zero Attempt on `kazhdan-group-algebra-tate-part-has-no-phantom`, the categorical form
  plus (P1) for `Γ` and for `Γ × Γ` gives that claim for `Γ`. The Tate phantom there comes from the
  non-nuclear `C*_r(Γ)`, so only the categorical form applies.
- Equivalent forms of square-zero-ness are in `z2-o2-phantom-tensor-square-is-sai-and-self-dual`.

## Attempts

- **Formal tensor-triangular argument (dies).**
  - Phantoms are the `θ = −1` layer, and tensor squares land in `θ = +1` (item 6 of
    `zp-restriction-trivial-splits-cellular-plus-phantom`).
  - A nonzero odd object with zero square is consistent with every formal relation available:
    `1 + χ = 1 + θ = 0`, `2` invertible, multiplicativity of `θ`.
  - Recalled analog, not imported: the Brown–Comenetz dual of the sphere has `I ∧ I ≃ *`.
  - So analytic input is needed.
- **Retraction (dies).** `j = id ⊗ 1 : D → D ⊗ D` is zero in `KK^G` for every phantom (item 1 of
  `o2-contractible-crossed-product-inner-half-flip-mcduff`). So `id_D` cannot factor through `D ⊗ D`
  along `j`.
- **Descent from a tensor factor (dies as a general principle).** `α ⊗ id_(O_2)` is always Rokhlin
  (item 4 of `z2-o2-phantom-tensor-square-is-sai-and-self-dual`). A proof must use that both factors
  carry `α`.
- **Relative McDuff extension (open; this is where it stops).**
  - `α` is Rokhlin iff the constant inclusion `O_2 → (O_2)_∞` extends along `a ↦ a ⊗ 1` to a unital
    equivariant \*-homomorphism `(O_2 ⊗ O_2, α ⊗ α) → ((O_2)_∞, α_∞)` (item 3 of the half-flip node).
  - Under square-zero, the source is the Rokhlin model. So this is a relative existence problem whose
    `KK^G`-obstruction vanishes.
  - Existence theorems of Gabe–Szabó type prescribe KK^G-classes, not restrictions to a subalgebra.
  - **O_3 descent is the same problem.**
    - Under square-zero, `O_3` embeds unitally in `F^(α⊗α)` (item 3(b) of
      `z2-o2-phantom-tensor-square-is-sai-and-self-dual`).
    - `α` is Rokhlin iff `O_3` embeds unitally in `F^α` (item 2(b) of
      `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`; passed ex-verify2-analysis part 15,
      d5b493c4bc).
    - The canonical map `F^α → F^(α⊗α)`, `x ↦ x ⊗ 1`, goes the wrong way.
    - A relative McDuff map `Ψ`, applied to central sequences of `O_2 ⊗ O_2`, gives after
      reindexation a unital map downward that carries `O_3` into `F^α`. Conversely, a McDuff map `ψ`
      gives `Ψ(a ⊗ b) = a ψ(b)`. So descent of `O_3` is equivalent to the extension problem.
    - In the "odd ⟹ even" language of the census: `α ⊗ α` is always even asymptotically inner
      (item 3(a) of the forms node). Square-zero adds exactly that its crossed product is contractible.
- **Construction (no candidate).** A square-zero phantom is a phantom, so it would answer Barlak–Li II,
  Remark 4.14(2), negatively for outer order-2 actions.
- **Z/4 square root (sufficient for square-zero; no converse).**
  - `γ = (α ⊗ 1) ∘ flip` generates a `Z/4`-action with `γ² = α ⊗ α`.
  - If `γ` is Rokhlin, `D` is square-zero.
  - `γ` is the multiplicative induction from `Z/2` to `Z/4` (recalled).

Artifact: `research/artifacts/uct-z2-square-zero-phantoms-2026-09-13.md` §3.
