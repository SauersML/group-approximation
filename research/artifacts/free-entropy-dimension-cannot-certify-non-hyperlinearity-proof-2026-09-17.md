# Import the Shlyakhtenko floor and the Mineyev--Shlyakhtenko ceiling, then embed algebraic cocycles in affiliated cocycles

*Attempt artifact (2026-09-17), formerly route `free-entropy-dimension-cannot-certify-non-hyperlinearity-proof` into `free-entropy-dimension-cannot-certify-non-hyperlinearity`, requires []. Demoted from the graph because referee lens 2 of three returned *refuted*: Steps 1--5 hold, but the Consequence paragraph and the section below claim that no free-entropy-dimension certificate can work on any hyperlinear group, a universal statement that items 1--3 do not prove, and the 'only published floor' and 'only ceiling' claims have no source. Lenses 1 and 3 returned *survives*. Restore it as a route once the Consequence is narrowed to the Theorem-3 floor versus the δ* ceiling and a full referee pass survives.*

Literature imports, followed by a short derivation.

## Sources (pinned 2026-09-17)

- **(S1)** Mineyev--Shlyakhtenko, *Non-microstates free entropy dimension for
  groups*, arXiv:math/0312242v2 (GAFA). The abstract, read on the arXiv page:

  > We show that for any discrete finitely-generated group G and any
  > self-adjoint n-tuple X_1,...,X_n of generators of the group algebra of
  > G, Voiculescu's non-microstates free entropy dimension δ*(X_1,...,X_n)
  > is exactly equal to β_1 (G)-β_0 (G)+1, where β_i are the L^2 Betti
  > numbers of G.

- **(S2)** Shlyakhtenko, *Lower estimates on microstates free entropy
  dimension*, arXiv:0710.4111v2, Introduction. Text was extracted from the
  PDF with pdfminer, and ligature glyphs came out garbled.
  - "It is known that δ0 ≤ δ∗"
  - "Theorem 3. Assume that Γ is embeddable into the unitary group of the
    ultrapower of the hyperfinite II1 factor. Then δ0(Γ) ≥ dimL(Γ) {c : Γ →
    CΓ cocycle}."

  The typeset set notation (the module generated, or its closure in `ℓ²Γ`)
  was not re-checked. Step 2 below covers both readings.

- **(S3)** Peterson--Thom, *Group cocycles and the ring of affiliated
  operators*, arXiv:0708.4327v2, §2, extracted with pdfminer.
  - Additivity: "dimLG M = dimLG M′ + dimLG M′′".
  - The exact sequence "0 → B1(G; M ) → Z 1(G; M ) → H 1(G; M ) → 0".
  - Theorem 2.2: "β(2) k (G) = dimLG H k(G, UG) = dimLG H k(G, ℓ2G) = dimLG H k(G, LG)".
  - Flatness: "LG ⊂ UG is a flat ring extension and ? ⊗LG UG preserves the
    dimension".
  - In a proof in §2: "dimLG Z 1(Gi; UG) = β(2) 1 (Gi) − 1/|Gi| + 1".

## Derivation

Let `Γ` be infinite and finitely generated. Cocycles `c(gh) = g c(h) + c(g)`
take values in left `Γ`-modules `CΓ ⊂ LΓ ⊂ ℓ²Γ ⊂ UΓ`. Right multiplication
by `LΓ` commutes with the left action, so every `Z^1(Γ; M)` below is a right
`LΓ`-module. By additivity (S3), `M' ⊂ M` implies `dim M' <= dim M`.

**Step 1: `dim Z^1(Γ; UΓ) = β_1^(2)(Γ) + 1`.**
- The map `UΓ → B^1(Γ; UΓ)`, `ξ ↦ ((g - 1)ξ)_g`, is right `LΓ`-linear and
  onto.
- Its kernel is zero. Write `ξ = a b^{-1}` with `a, b ∈ LΓ` and `b` a
  non-zero-divisor. Then `gξ = ξ` for all `g` forces `g a = a` for all `g`,
  with `a ∈ ℓ²Γ`. Hence `a = 0`, because `Γ` is infinite.
- So `dim B^1 = dim UΓ = dim LΓ = 1`, by flatness (S3).
- Additivity on the exact sequence and Theorem 2.2 give
  `dim Z^1(Γ; UΓ) = 1 + β_1^(2)(Γ)`. This agrees with the last quotation in
  (S3) for `G_i = G` infinite.
- `β_0^(2)(Γ) = 0` for infinite `Γ`, so (S1) reads `δ*(X) = β_1^(2)(Γ) + 1`.

**Step 2: `a(Γ) <= δ*(X)`.**
- `Z^1(Γ; CΓ) ⊂ Z^1(Γ; UΓ)`, so the `LΓ`-module it generates lies in
  `Z^1(Γ; UΓ)`. Monotonicity and Step 1 give `a(Γ) <= β_1^(2)(Γ) + 1`.
- Under the other reading of (S2), take the closure of the algebraic cocycles
  in `Z^1(Γ; ℓ²Γ)` for the pointwise topology. It is still a submodule of
  `Z^1(Γ; ℓ²Γ) ⊂ Z^1(Γ; UΓ)`, so the same bound holds.

**Step 3: `a(Γ) >= 1`.**
- For `ξ ∈ CΓ`, the inner cocycle `c_ξ(g) = (g - 1)ξ` is algebraic, and
  `c_ξ · x = c_{ξx}`.
- So the generated module contains `{c_x : x ∈ LΓ}`. By the kernel
  computation of Step 1, this is isomorphic to `LΓ`, which has dimension `1`.

This proves item 1 of the claim.

**Step 4: item 2.** If `Γ` is hyperlinear, Theorem 3 of (S2) gives
`δ_0(X) >= a(Γ)`, and (S2) with (S1) gives `δ_0(X) <= δ*(X)`.

**Step 5: item 3 (torsion).**
- Suppose `g_1, ..., g_m` generate `Γ` and `g_i` has order `n_i`. The
  evaluation `c ↦ (c(g_1), ..., c(g_m)) ∈ UΓ^m` is right `LΓ`-linear and
  injective, since the cocycle identity and
  `c(g^{-1}) = -g^{-1} c(g)` determine `c` from its values on generators.
- From `g_i^{n_i} = 1` we get
  `0 = c(g_i^{n_i}) = (1 + g_i + ... + g_i^{n_i - 1}) c(g_i) = n_i E_i c(g_i)`.
  Here `E_i ∈ LΓ` is the averaging projection of `<g_i>`, with
  `τ(E_i) = 1/n_i`.
- So `c(g_i) ∈ (1 - E_i) UΓ`, and flatness gives
  `dim (1 - E_i) UΓ = τ(1 - E_i) = 1 - 1/n_i`.
- Monotonicity and Step 1 give `β_1^(2)(Γ) + 1 <= Σ_i (1 - 1/n_i)`.

## Why this is the kill step

A `δ_0` certificate of non-hyperlinearity has the shape "if microstates exist
then `L <= δ_0(X) <= U`" with `L > U`.
- The only published floor for group generators is (S2) Theorem 3. Jung's
  `δ_0 >= 1` for diffuse embeddable algebras is the inner-cocycle part of it,
  Step 3.
- The only ceiling valid for all groups is `δ_0 <= δ*`.
- Steps 1--3 prove `L = a(Γ) <= U = δ*(X)` from algebra alone, for every
  infinite finitely generated group. So the comparison never crosses.
- Step 5 shows that exponent laws, one generator at a time, cannot pull the
  ceiling below the floor either.

Any other floor `L' > δ*(X)` contradicts item 2 on every hyperlinear group.
Proving it is therefore the same as proving the microstate spaces empty.
