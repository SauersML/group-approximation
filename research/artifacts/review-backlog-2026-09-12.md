# Review backlog, 2026-09-12

Lane `review-backlog`. Adversarial review of ESTABLISHED claims landed since about 12:00 without an
independent verdict, taken in order of consequence: first the routes into `non-hyperlinear-group`,
`nonsofic-hyperbolic-group`, Boone–Higman, p_c < p_u and Strong Atiyah, then the rest. Claims already
covered by `review-swarm2-2026-09-12.md`, `review-bh-swarm-2026-09-12.md`,
`review-major-swarm-2026-09-12.md` and `review-reviewer2-queue-2026-09-12.md` are skipped.

Verdicts: PASS (the proof holds as written, up to stated trust surfaces), GAP (a step is asserted but not
proved, and the conclusion is not known false), FAIL (a step or the conclusion is false).

## 1. `compressor-transport-exactifies-under-vertex-rounding` (2eda8abf6): PASS

Checked item by item against `compressor-transport-exactifies-proof`.

- **Defect.** `σ(A)σ(s)σ(A)^(-1) = σ(AsA^(-1))`, and `AsA^(-1)` is a fixed element of `Λ ⊆ Γ`, hence a fixed
  word in `F_Γ`. A homomorphism `π_n` rounding an asymptotic homomorphism on generators rounds it on any
  fixed word, with error at most word length times the generator error. So `δ_n → 0`.
- **Kazhdan step.** For the representation `Φ(γ)X = ρ_n(γ)Xπ_n(γ)^*` on `(M_(n'), ||·||_2)`, the vector
  `X − EX` is orthogonal to the invariants and has the same displacements as `X`. So
  `||X − EX||_2 <= κ^(-1) max_s ||Φ(s)X − X||_2`, and `||Φ(s)U − U||_2 = ||ρ_n(s)U − Uπ_n(s)||_2` is the
  defect. Property (T) of `EL_r(F_q[x_1..x_d])`, `r >= 3`, is Ershov–Jaikin-Zapirain.
- **Contraction.** `π_n` and `ρ_n = π_n ∘ Ad A` factor through finite groups, so `E` is a finite average of
  maps `X ↦ ρ(γ)Xπ(γ)^*`. So `||T||_op <= 1`, where `T = E(U_n)`.
- **Support.** `1 − T^*T = U^*(U − T) + (U − T)^*T`, so `||1 − T^*T||_2 <= 2δ_n/κ`. On `1 − Q` the operator
  `T^*T` vanishes, so `τ(1 − Q) = ||(1 − T^*T)(1 − Q)||_2^2 <= 4δ_n^2/κ^2`.
- **Invariance and polar part.** `Tπ(γ) = ρ(γ)T` gives `T^*ρ(γ) = π(γ)T^*`, hence `T^*T ∈ π(Γ)'`. So
  `Q ∈ π(Γ)'`, `W = T|T|^(-1)` intertwines on `Q`, and ranks agree in finite dimension.
- **Spectral measures.** `ρ_n|e_12` has spectral measure `(D_A)_*μ_n`. For a spectral projection `P_E`
  commuting with `Q`, `μ_n(E) = τ(P_E Q) + τ(P_E(1 − Q))` with the second term in `[0, τ(1 − Q)]`. The same
  holds for `ρ` and `Q'`, and the first terms agree through `W`. So
  `|μ_n(E) − μ_n(D_A^(-1)E)| <= τ(1 − Q)`.

Bookkeeping, no effect on the conclusion: `σ_n(A)` lives in `M_n` and `π_n` on `C^(n')` with
`n'/n → 1`. The unitary representative must be taken in `U(n')`, as (H1) allows.

## 2. `nonunit-projection-bounded-by-root-spectral-mass` (2eda8abf6): PASS

- **Product splitting.** `St_r(A_u × A_nu) = St_r(A_u) × St_r(A_nu)` for `r >= 3`. I re-derived the one
  non-obvious relation: `x_ij((a,0))` commutes with `x_ji((0,b))`, because `x_ji((0,b)) = [x_jk((0,b)), x_ki((0,1))]`
  and `x_ij((a,0))` commutes with both factors by the Steinberg relations, since `(a,0)(0,b) = 0`.
- **Fixed space.** Irreducibles of a direct product are tensor products, so a constituent is trivial on the
  normal factor or has no invariant vector there. Hence `range P = ∩_(i≠j) Fix(x_ij(A_nu))`.
- **Weyl symmetry.** Conjugation preserves fixed-space dimension.
- **Count.** Codimensions of an intersection are subadditive.
- **Both directions.** `range P ⊆ Fix(e_12(A_nu))` also gives the reverse inequality
  `μ(χ|A_nu ≠ 1) <= τ(1 − P)`. So the "equivalent" in the Reading is correct: `τ(1 − P) → 0` iff the
  non-unit root mass `→ 0`.

## 3. `pure-nonunit-root-mass-is-log-scale-folner` (2eda8abf6): PASS

- **Item 1.** In `B_n = A_u × A_nu`, `z = x_1⋯x_d` is a unit on `A_u` and lies in the maximal ideal of every
  factor of `A_nu`, hence is nilpotent there. So `z^k B_n = A_u × z^k A_nu`, and a finite depth means
  triviality on `A_u`.
- **Item 2.** `φ_A(z) = x^(A·1)`, where every coordinate of `A·1` is at least `d` because all entries of `A`
  are `>= 1`. So `φ_A(z^k R_+) ⊆ z^(dk) R_+`, and triviality on `z^m R_+` transfers to `χ ∘ φ_A` once
  `dk >= m`.
- **Item 3.** `D_A^(-1){depth <= d^j} ⊇ {depth <= d^(j+1)}` by item 2. Item 3 of claim 1 then gives
  `F_(j+1) <= F_j + η_n`.
- **Item 4.** The kernel ideals of the root subgroups coincide by Weyl symmetry. `B_n` embeds additively
  in `∏_(i≠j) π_n(e_ij(R_+))`. Each factor is an elementary abelian `p`-subgroup of `U(n')`, which is
  simultaneously diagonalizable and so has `F_p`-dimension at most `n'`. Strict descent of `z^k A_nu`
  bounds finite depth by `dim_(F_p) A_nu <= r(r−1)n'`.
- **Reading.** The rate statement `δ_n^2 log n → 0` is correct.
