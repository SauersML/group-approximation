# Tensor towers: Question 3.14 as soft splitting of tail bundles (2026-09-12, part 2)

Lane `ex-tw-projection-starved-bundle`. Continues
`research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md`, whose conventions and Theorem A
are used.

**Outcome.** No witness. Unreviewed.
1. **Proposition T.** For fibred tensor towers `A = ⊗_k End(W_k)`, triviality of the W*-bundle is
   equivalent to a purely topological condition: every tail bundle `⊠_{n<k≤m} W_k` admits an
   `ε`-soft half splitting. Such a splitting is a positive section with small idempotence defect and
   trace `1/2` at every point.
2. **A concrete witness shape** for BBSTWW Question 3.14. It needs a tower of indecomposable
   multiplicity bundles whose tails cannot be softly split. Dimension counting forces
   `dim Π_{n<k≤m} Y_k > rank ⊠_{n<k≤m} W_k`, which is superlinear dimension growth in the tail rank.
   This is the regime of Toms's Thom–Porteous obstructions.

## 1. Setting

- For `k ≥ 1`, `Y_k` is a compact metrizable space and `W_k → Y_k` a complex vector bundle of rank
  `w_k ≥ 2`.
- `Z_m = Π_{k≤m} Y_k`, and `U_{n,m} = ⊠_{n<k≤m} W_k` is pulled back to `Z_m`, of rank `R_{n,m} = Π_{n<k≤m} w_k`.
- `A_m = C(Z_m, End(U_{0,m}))`, with unital maps `a ↦ a ⊗ 1_{W_{m+1}}`, and `A = lim A_m`.
- `A` is a `C(X̂)`-algebra over `X̂ = Π_k Y_k`, with UHF fibres. A trace of `A` is a compatible
  family of measures on the `Z_m`, so `T(A) = Prob(X̂)`. It is Bauer, with `∂_e T(A) = X̂`.
- Every fibre factor is `R`: `A` is nuclear, and the ranks tend to infinity.
- `M` is the strict closure, a W*-bundle over `X̂` (`closed-extreme-trace-sets-give-r-fibre-w-star-bundles`
  with `K = X̂`).
- `tr` is the normalized trace on each fibre, and `‖x‖_2 = tr(x*x)^{1/2}` pointwise.

**Definition.** Let `U` be a vector bundle of rank `R` over `Z`. An *`ε`-soft half splitting* of `U` is
a positive contraction `h ∈ C(Z, End(U))` with, at every `z ∈ Z`:

```text
tr(h(z) − h(z)²) ≤ ε,        |tr h(z) − 1/2| ≤ ε.
```

- `ε = 0` means `U = P ⊕ P'` with `rank P = rank P'`.
- If `dim Z ≤ R`, general position gives a trivial subbundle of rank `R − ⌈dim Z/2⌉ ≥ R/2`, so an
  exact splitting exists.

## 2. Proposition T

**Proposition T.** `M ≅ C_σ(X̂, R)` if and only if, for every `n` and `ε > 0`, there is `m > n` such
that `U_{n,m}`, pulled back to `Z_m`, admits an `ε`-soft half splitting.

*Proof.*
- **(⟸).** Let `h` split `U_{n,m}` over `Z_m` with defect `ε_n → 0`, and put `p = 1 ⊗ h ∈ A_m`.
  - `p` commutes exactly with `A_n ⊗ 1`, with `tr(p − p²) ≤ ε_n` and `|tr p − 1/2| ≤ ε_n` at every
    point, hence for every trace.
  - Norm density of `∪_n A_n` makes `(p)` central in `‖·‖_{2,u}`.
  - This is condition (ii) of Ozawa's Theorem 15, so `M` is trivial.
- **(⟹).** If `M` is trivial, Ozawa (i) ⟹ (ii) gives `p_j ∈ M` as in (ii).
  - `A` is `‖·‖_{2,u}`-dense, and norm-bounded functional calculus lets us assume each `p_j` is a
    positive contraction in some `A_m`.
  - Fix `n` and `δ > 0`. Choose open sets `V_α` covering `Z_n` on which `U_{0,n}` is trivial, with local
    matrix units `e^α_{ij}` (`i, j ≤ d = R_{0,n}`) and a partition of unity `f_α`.
  - The finitely many elements `f_α e^α_{ij}` lie in `A_n`.
  - Let `Φ = tr_{U_{0,n}} ⊗ id` be the fibrewise partial trace, a continuous conditional expectation
    onto `1 ⊗ End(U_{n,m})`. On `V_α`, `x − 1 ⊗ Φ(x) = d^{-1} Σ_{i,j} e^α_{ij}[e^α_{ji}, x]`. With `f_α`
    central and `Σ_α f_α = 1`, this gives
    `‖x − 1 ⊗ Φ(x)‖_{2,u} ≤ C_n max_{α,i,j} ‖[f_α e^α_{ji}, x]‖_{2,u}`.
  - Take `j` with the right side below `δ` for `x = p_j`, and `tr(p_j − p_j²) ≤ δ` everywhere.
  - Put `h = Φ(p_j)`, a positive contraction section of `End(U_{n,m})` over `Z_m`. Then:
    - `tr h = tr p_j`;
    - `tr(h − h²) ≤ tr(p_j − p_j²) + 2‖p_j − 1 ⊗ h‖_2 ≤ 3δ`.
  - So `h` is a `3δ`-soft half splitting. ∎

**Consistency checks.**
- Split multiplicity bundles `W_k = θ ⊕ L_k` give `U_{n,m} = ⊕_v L_v`, which splits exactly. That
  recovers Hirshberg–Rørdam–Winter products and the single-projection variant of Toms's tower
  (`block-balanced-towers-have-central-halving`).
- If `dim Π_{n<k≤m} Y_k ≤ R_{n,m}` for some `m`, the tail splits exactly. So a witness needs
  superlinear dimension growth in the tail rank at every `n`.

## 3. What a witness needs, and tools

- **Indecomposable multiplicity bundles.** No `W_k` may split into equal ranks. Beyond that, no tail
  may carry a square `V ⊕ V`: if `U_{n+1,m} ≅ V ⊕ V ⊕ G` with `rank G` small, then
  `W_{n+1} ⊠ U_{n+1,m} ≅ (W_{n+1} ⊠ V)^{⊕2} ⊕ (W_{n+1} ⊠ G)` splits with small defect.
- **Robust obstructions exist in this regime.** Toms (arXiv:2606.12188v2, Section 6) obstructs
  2-norm-approximate equivalence by Thom–Porteous classes at quadratic dimension growth. These
  obstructions survive tracial approximation; coordinate Euler mass does not (Corollary D of part 1).
- **Why soft is harder than exact (heuristic).** The space of `ε`-soft half projections in `M_R`
  retracts onto Grassmannians `Gr(k, R)`, `|k − R/2| ≤ εR`, glued along partial flags.
  - Gluing adjacent Grassmannians along `Fl(k, k+1; R)` kills `H_2`:
    `H_2(Fl) ≅ Z² → H_2(Gr_k) ⊕ H_2(Gr_{k+1})` is an isomorphism, by the pairings with `c_1(S_k)`
    and `c_1(S_k) + c_1(L)`.
  - So tautological Chern classes do not survive in the glued space. An obstruction must use
    characteristic classes of `U` itself in degrees above about `εR`, together with unstable
    information.
  - Not proved.
- **Open target.** `some-tensor-tower-has-unsplittable-tails`.

## Trust surfaces

- Proposition T uses Ozawa's Theorem 15 (verbatim on `r-fibre-bundle-triviality-halving-citation`),
  the face-bundle claim of part 1, and elementary matrix identities. It is not reviewed, and nothing is
  in Lean.
- Section 3 is analysis, not theorems.
