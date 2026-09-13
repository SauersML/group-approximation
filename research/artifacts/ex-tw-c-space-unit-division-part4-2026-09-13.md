# Strict comparison divides the unit over C-space tracial boundaries, part 4: linear weights and a metric criterion (2026-09-13)

Lane `ex-tw-rotation-gluing`. Continues parts 1–3 (`research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md`
and its `-part2`, `-part3` files). Not reviewed.

**Outcome.**
- **Proposition 8.2.** In Theorem E(a) the weights `(1/N + δ)^{1/2}` can be replaced by `1/N + δ`. A refined
  spectral lower bound removes the cutoff loss that forced square roots.
- **Corollary F.** Metric criterion: the unit divides unless local divisions of precision `ω = 1/N + δ`
  are confined to sets so small that covers of that mesh need order at least `c/ω`.
  - On the Hilbert cube with the weighted `ℓ¹` metric, the confinement must be exponentially small in `1/ω`.
  - Heuristically, a division with `N` matrix units must pin at least `cN` coordinates. This is the same
    linear relation between matrix size and dimension as the ASH gluing obstruction recorded on
    `ash-strict-comparison-rank-gap-algebra-exists`.

Setting as in Section 6: `A` is unital, simple, separable, exact and non-elementary, with strict comparison
and a nonempty Bauer simplex with boundary `K`.

## 8. Linear weights

**Lemma 8.1.** For a positive contraction `b`, a tracial state `λ` and `0 < σ ≤ 1/2`:
```text
μ_{b,λ}((σ,1])  ≥  λ(b) − 2 λ(b − b²).
```
*Proof.*
- `λ(b) ≤ ∫_{(0,σ]} x dμ + μ((σ,1])`.
- On `(0,σ]` we have `x ≤ (x − x²)/(1 − σ) ≤ 2(x − x²)`. ∎

**Proposition 8.2.** The unit of `A` is tracially `N`-divisible for every `N` iff for every `κ > 0` some finite
family of division sets `(O_i, φ_i, N_i, δ_i)` covers `K` with
```text
Σ_{i : λ ∈ O_i} (1/N_i + δ_i)  ≤  κ      for every λ ∈ K.
```

*Proof.*
- **(⟹).** Take `K` alone at large `N` and small `δ`.
- **(⟸).** Fix `n` and `t, γ` as in Section 3 of part 2. Put `ε_0 = γ/2 ≤ 1/8` and `s = ε_0/8`, and take a
  family as above with `κ = ε_0²/64`, members `i = 1, …, m`.
  - Choose a partition of unity `supp h_i ⊆ O_i`.
  - Build the staircases `B_i` (Lemma 3 of part 1) at the precision `(N_i, δ_i)` of each member. Put
    `d_i = 1/(4N_i) + δ_i ≤ 1/N_i + δ_i`.
  - Choose `η` with `16mη/s ≤ ε_0/8`, and approximants `b_i ∈ A` with `‖b_i − B_i‖_{2,u} ≤ η`.
  - Use the same cutoff `x_i = (b_i − s)_+` for every member.
  - The moves and cuts are those of Section 3. The cut levels satisfy `σ_i ∈ [s, 1/2]`.

**Per-member bounds**, for `σ ∈ [s, 1/2]`:
- **Upper, active member.** By (F2) at `s`:
  `μ_{b_i,λ}((σ,1]) ≤ t h_i(λ)(1 + 2s) + 2η + 2(d_i + 3η)/s`.
- **Upper, inactive member.** `μ_{b_i,λ}((σ,1]) ≤ η(1 + 2s) + 6η/s ≤ 8η/s`.
- **Lower, all members.** By Lemma 8.1: `μ_{b_i,λ}((σ,1]) ≥ t h_i(λ) − δ_i − η − 2(d_i + 3η)`.
  When summing, apply this only to active members and use `μ ≥ 0` for inactive ones, because `Σ_i δ_i` over
  all members is not bounded by `κ` (review note, `research/artifacts/ex-review2-analysis-2026-09-13-part2.md`).

**Summing at `λ`.** A member is active only if `λ ∈ O_i`, so `Σ_{i active} d_i ≤ κ`. Hence:
```text
upper:  Σ_i μ_{b_i,λ}((σ_i,1])  ≤  t + 2st + 2κ/s + 16mη/s  ≤  t + ε_0/4 + ε_0/4 + ε_0/8,
lower:  Σ_i μ_{b_i,λ}((σ_i,1])  ≥  t − 3κ − 7mη             ≥  t − ε_0/8 − ε_0/8.
```
- **Margins.** The margin in every move is at least `1 − t − 5ε_0/8 ≥ 1/8`, since `t ≤ 3/4` and
  `ε_0 ≤ 1/8`. So strict comparison applies as in Step 5.
- **Conclusion.** The final orthogonal sum `W` has `|d_τ(W) − t| ≤ 5ε_0/8 < γ` at every trace, and Step 7
  applies. ∎

**Remark.** Parts 1–3 used the cutoff `s_i = d_i^{1/2}` per member, and the bound `λ(b) − σ` charged each
member its cutoff. Lemma 8.1 charges only the defect. The overshoot `2st` from the factor `(1 + 2s)` is
global, because the `h_i` sum to `1`.

## 9. A metric criterion

Fix a compatible metric on `K`.
- `𝒟_A(ω)`: the open sets `O ⊆ K` carried by a division set with `1/N + δ ≤ ω`. By Lemma 1 this is an open
  cover of `K`.
- `ℓ_A(ω) > 0`: its Lebesgue number, so every set of diameter `< ℓ_A(ω)` lies in a member.
- `ord_K(r)`: the least `k` such that `K` has a finite open cover by sets of diameter `< r` in which every
  point lies in at most `k` members.

**Corollary F.** If `liminf_{ω → 0} ω · ord_K(ℓ_A(ω)) = 0`, then the unit of `A` is tracially `N`-divisible
for every `N`.

*Proof.*
- Given `κ`, choose `ω` with `ω · ord_K(ℓ_A(ω)) ≤ κ`.
- Take a finite open cover of mesh `< ℓ_A(ω)` and order `ord_K(ℓ_A(ω))`.
- Each member lies in a member of `𝒟_A(ω)`, so it is itself a division set of weight at most `ω`.
- At every point the weights sum to at most `ω · ord_K(ℓ_A(ω)) ≤ κ`. Apply Proposition 8.2. ∎

**Examples.**
- **`dim K = d < ∞`.** `ord_K(r) ≤ d + 1` for all `r` (covering dimension), so the criterion always holds.
  This recovers the finite-dimensional case for exact algebras.
- **Hilbert cube** `Q = [0,1]^ℕ` with `ρ(x,y) = Σ_i 2^{−i}|x_i − y_i|`. Then `ord_Q(r) ≤ log_2(4/r) + 2`.
  - Put `D = ⌈log_2(4/r)⌉`.
  - The cube `[0,1]^D`, with the restriction of `ρ`, has covering dimension `D`. So it has finite open
    covers of mesh `< r/2` and order `D + 1`.
  - Pull them back along the coordinate projection. The tail coordinates add at most
    `Σ_{i>D} 2^{−i} = 2^{−D} ≤ r/4` to diameters.
  - So Corollary F gives division whenever `ℓ_A(ω) ≥ exp(−o(1/ω))`.
- **What a witness over `Q` must satisfy.** Suppose the unit does not divide.
  - Corollary F gives `c > 0` with `ω · ord_Q(ℓ_A(ω)) ≥ 2c` for all small `ω`.
  - So `log_2(4/ℓ_A(ω)) + 2 ≥ 2c/ω`, and `ℓ_A(ω) ≤ 16 · 2^{−2c/ω} ≤ 2^{−c/ω}` for all small `ω`.
  - Every cover by division sets of weight `ω` needs sets of `ρ`-diameter that small.
  - With `ω ≈ 1/N`, heuristically: some division sets of matrix size `N` must be thin in at least about `cN`
    of the leading coordinates.

**Comparison with the ASH gluing heuristic** (`ash-strict-comparison-rank-gap-algebra-exists`). There, extending
a twisted boundary field over a top cell is "obstructed when `δ` times the block size is below about half the
cell dimension".
- That is a linear relation between matrix size and dimension.
- Corollary F says a strict-comparison witness on a Bauer simplex needs such a linear relation for its local
  divisions. A logarithmic one cannot do.
- Neither statement constructs a witness.

## 10. The division locus sits inside the bundle locus

**Proposition 10.1.** Let `A` be as above and nuclear, with strict closure `M`, a hyperfinite W*-bundle over
`K`. Let `Z(M)` be the set of points with no closed neighbourhood `Y` with `M_Y ≅ C_σ(Y, R)`. Then
`Z_sum(A) ⊆ Z(M)`.

*Proof.* Let `Y` be a closed neighbourhood of `λ_0` with `M_Y` trivial. Fix `N`.
1. Constant matrix units of `M_N ⊂ R` define a unital `*`-homomorphism `M_N → M_Y`.
2. The restriction quotient `q_Y: M → M_Y` is onto, and `π_λ = π_λ^Y ∘ q_Y` for `λ ∈ Y`. This is the
   Evington–Pennig restriction recorded on `bauer-gamma-failure-localizes-proof`, step 4.
3. Lift the matrix units to contractions of `M`, and approximate them in `‖·‖_{2,u}` by elements of `A`.
   Their relation defects tend to `0` in `sup_{λ∈Y} ‖·‖_{2,λ}`.
4. So they define a unital `*`-homomorphism into `ℓ^∞(A)/c_Y`, where `c_Y` is the ideal of sequences
   `(x_n)` with `lim_ω sup_{λ∈Y} ‖x_n‖_{2,λ} = 0`.
5. Order zero lifting gives `φ_n: M_N → A` with `sup_{λ∈Y} λ(1 − φ_n(1)) → 0`.
6. Hence `Y` carries division sets at every precision, so `Y` is summably divisible, so `λ_0 ∉ Z_sum`. ∎

**Combined picture** (nuclear `A`, strict comparison, Bauer simplex).
- `Z_sum(A) ⊆ Z(M) ∩ K^{(C,∞)}`.
- `Z(M) ⊆ K^{(∞)}` (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`).
- The unit divides iff `Z_sum(A) = ∅`.
- Uniform Gamma holds iff `Z(M) = ∅`.
- Nonempty `Z_sum(A)` means the unit does not divide, so `A` has strict comparison without being
  `Z`-stable: a Toms–Winter counterexample.
- Under tracially locally finite nuclear dimension, `Z(M) ≠ ∅` together with `Z_sum(A) = ∅` is impossible,
  because a divisible unit gives uniform Gamma (`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`).
  So on that locus `Z_sum(A) = ∅` iff `Z(M) = ∅`.

**Metric dependence.** The criterion holds for every compatible metric, and a witness must defeat all of
them. If the unit does not divide, then `liminf_{ω→0} ω · ord_{K,ρ}(ℓ_{A,ρ}(ω)) > 0` for every compatible
metric `ρ`. Only this direction is asserted.
