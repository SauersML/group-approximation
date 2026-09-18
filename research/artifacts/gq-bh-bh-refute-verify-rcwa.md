# Adversarial check: `rcwa-groups-satisfy-boone-higman` (bh-refute, 2026-09-18)

Rotation item 2 (222a364e8). This is a hand re-derivation of every lane step of
`rcwa-groups-bh-via-sign-doubling-and-odometer-host-proof`. Li's Example ex:ZS (III) was
re-read at source (`gq/src/kep/li-garside-II-2110.04505v2.tex`, l.2371–2380), in the same session as the
tree-lattice check. Matui's Theorem simple2, FKPS homology and Li's AH theorem are taken as imported.

Verdict: **PASS**. No gap was found.

## Step 1 (sign doubling)

- **Cocycle.** `ε_{gh}(n) = ε_g(h(n)) + ε_h(n)`, since slopes multiply. So `g·(n,i) = (g(n), i + ε_g(n))` is a
  faithful action.
- **All four rows of the table re-derived.** The slopes in `u` are `σ`, `−σ`, `σ`, `−σ` with the sign making
  each positive (the chain rule gives `−2 · (−1/2) = 1` in rows 3–4). Classes mod `m` become classes mod `2m`.
  Multipliers and divisors are unchanged up to sign, so `δ(RCWA_P) ⊆ RCWA_P`, using `2 ∈ P'`.

## Step 2 (extension to `Ẑ_P`)

- **Images of classes.** On `r_i(m)` an increasing affine bijection has consecutive differences
  `n_i = (a_i/c_i) m`, which is an integer because the values are integers and `P'`-smooth. So the image is a
  full class `s_i(n_i)`, and `h(r_i + tm) = s_i + (t + c_i) n_i` with `c_i ∈ Z`.
- **Boxes.** `r + mẐ_P` is the closure of `r(m)`, since `m` is `P'`-smooth. Boxes meet iff classes meet.
  Disjoint boxes whose union is closed and contains `Z` partition `Ẑ_P`.
- `ĥ` is a homeomorphism, and `h ↦ ĥ` is an injective homomorphism by density.

## Step 3 (the host and the embedding)

- **The odometer action.** `r + mz + n = ((r+n) mod m) + m(z + ⌊(r+n)/m⌋)`. It is consistent on composites,
  and the binary colour is fixed with restriction `a^n`. The two factorizations of `(λ, w)` give the same
  image and the same restriction. It is degree-preserving.
- **Right cancellation of `D = Λ ⋈ Z`, re-derived.** Suppose `μ(a^n·ν) = μ'(a^{n'}·ν)` and the restrictions
  agree. Then unique factorization gives `μ = μ'`. Equal residues and equal carries give `n = n'`.
  So (F) holds by Li l.1456.
- **The embedding.** On `B(r_i, m) × C`, the element `ι(g)` is `μ y ↦ λ(a^{c_i}·y)` with
  `μ = ((m, r_i), ∅)` and `λ = ((n_i, s_i), ∅)`. Checked pointwise: `(r_i + mz, w) ↦ (s_i + n_i(z + c_i), w)`.

## Step 4 (effective, Hausdorff, essentially principal, minimal, purely infinite)

- **Effective.** The identity on `μνX` forces equal moduli, then `c = 0`, then equal paths, then a strong fixed
  point, so `n = 0`. Checked.
- **Hausdorff.** Unit-germ sets are `μX` or `∅`. Checked in both the equal-degree and unequal-degree cases.
  Fixed sets of `(m_μ − m_λ) z = const` are singletons in each `Z_q`.
- **Minimal and purely infinite.** These are the standard cylinder arguments, as in the refereed `2V_τ` route.

## Step 5 (`F_∞`)

Li Ex. (III) applies, and each hypothesis was checked against the TeX:
- one-vertex finite `(k+1)`-graph;
- at least 2 edges of each colour (`p >= 2` edges of colour `p`, and 2 binary);
- degree-preserving action;
- (F) holds;
- `D^*(v,v) = St(Z, v) = Z`, which is of type `F_∞` (rem:ZS-Stab).

Li himself notes (end of Ex. ZS) that for `G = Z` condition (F) is not even needed.

## Step 6 (perfect, hence simple)

- **Normal form.** `f = h ∏ σ_{μ_i}^{n_i}`. Checked that `σ_μ^n = (μ y ↦ μ(a^n·y))`.
- **`[[G_Λ]]^{ab} = 0`.**
  - The FKPS chain complex of a one-vertex `k`-graph is the Koszul complex on the integers `1 − n_i`.
  - The binary colour has `1 − 2 = −1`, a unit, so the complex is acyclic.
  - Li's AH sequence then gives ab = 0.
- **The `σ_μ`.**
  - All `σ_μ` for proper cylinders are conjugate. The complements are equalized by binary splits.
  - `σ_μ = σ_{μ(∅,0)} σ_{μ(∅,1)}`, since the binary letter is fixed with restriction `a`. So `c = 2c`, hence
    `c = 0`.
  - The same holds for `σ_∅`.
- So `H_P^{ab} = 0`, and Matui gives simplicity of `D(H_P) = H_P`.

## Attacks tried (all failed)

- **Decreasing pieces with nonzero flux.** Doubling makes them increasing. The flux becomes shifts `±c`,
  realized by `σ`'s. Calibrated on `n ↦ n+1` and `n ↦ −n−1`.
- **A non-integral `n_i` or shift.** Excluded by integrality of consecutive values.
- **Hidden reliance on `CT_P`'s nonnegativity.** Not used. Step 2 needs only increasing slopes.
