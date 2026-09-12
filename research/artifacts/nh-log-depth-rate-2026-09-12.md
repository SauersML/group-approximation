# Log-depth rate for vertex rounding: equivalence with unit type, and why the suggested tools give no rate

Lane `nh-log-depth-rate`, 2026-09-12. Target: `vertex-rounding-with-log-depth-rate`.

Notation is that of `nonunit-root-mass-log-depth-scale-bound`:
- `Γ = EL_r(R_+)`, `R_+ = F_q[x_1..x_d]`, `G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, `r, d >= 3`;
- (H1) roundings `π_n`, compressor defect `δ_n`, `η_n = 4δ_n^2/κ^2`, and torus defect `η_n^t`;
- `μ_n`, the normalized spectral measure of `f -> π_n(e_12(f))`;
- `P_n`, the unit-type projection, and `D_n = D(π_n)`, the maximal non-unit depth.

## 1. Result

**Theorem** (claim `log-depth-rate-rounding-is-equivalent-to-unit-type`, route
`log-depth-rate-unit-type-equivalence-proof`). For a fixed trace-preserving `σ`, the following are equivalent:
- (a) (H1) with `δ_n^2 log(1 + D_n) -> 0`;
- (b) (H1) with unit-type roundings;
- (c) (H1) with `μ_n(depth_nu > 1) -> 0`.

**Proof.**
- **(a) ⟹ (c).** Item 1 of the scale bound gives `μ_n(depth_nu > 1) <= η_n(1 + log_d max(1, D_n))`, and
  this tends to 0 under (a).
- **(c) ⟹ (b).**
  - The shallow part obeys `μ_n(depth_nu = 1) <= q·η_n + η_n^t -> 0`, by item 5 of
    `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`.
  - `nonunit-projection-bounded-by-root-spectral-mass` gives `τ(1 - P_n) -> 0`.
  - Trivialize the non-unit constituents. This moves each generator by at most `2·τ(1 - P_n)^(1/2)`.
- **(b) ⟹ (a).** Unit type means `A_nu = 0`, so `D_n = 0`, and `δ_n <= 2` makes the product 0.

The route in Cairn proves (a) ⟹ (b) through item 3 of the scale bound, which is this chain (a) ⟹ (c) ⟹ (b).

## 2. What this changes

- **Not a quantitative strengthening.** `vertex-rounding-with-log-depth-rate` was recorded as a quantitative
  form of (H1) that implies the crux. It is equivalent to the crux, because unit-type roundings meet the
  rate trivially.
- **Both directive branches reduce to the crux.**
  - "Prove the rate" is "prove unit-type rounding".
  - "Build a model where the defect cannot beat log D" is "find `σ` satisfying (H1) for which unit-type
    rounding fails".
- **For the supplied roundings.** A rate asserted for every (H1) rounding would be stronger. That form is
  not opened here.
- **Dichotomy for any (H1) family.** Either
  - `μ_n(depth_nu > 1) -> 0`, and then the family can be replaced by a unit-type one with `D = 0`; or
  - `lim_U μ_n(depth_nu > 1) = c > 0`.

  In the second case `D_n >= d^(c/η_n - 1)`, and by `root-character-nonunit-depth-at-most-log-q-dimension`
  some constituent has dimension at least `q^(D_n)`.

## 3. The suggested tools, and why none gives a rate

These are assessments. None is a Cairn claim.

**3.1 Heisenberg atom count.**
- Lemma 2.1 of `nh-h1-quantitative-2026-09-12.md` gives `q^(depth_nu(χ)) <= |B/J_χ| <= N·μ_n({χ})`.
- This puts a floor on deep atoms, `q^(depth)/N`, and caps `D_n <= log_q N`. Both statements scale with `N`.
- The amplification `σ -> σ ⊗ 1_m` multiplies `N` and leaves `μ_n`, `δ_n` and `D_n` unchanged. So no
  intrinsic bound on deep mass follows, only the rate `δ_n^2 log log n -> 0` stated in `n`.

**3.2 Truncation at a fixed depth.**
- For each fixed `K`, the mass at depth at most `K` vanishes along `U`.
- The tail `(K, D_n]` is still paid block by block at `η_n` per d-adic block, which is the `log D` count again.
- Letting `K = K_n` grow is itself a rate condition on `δ_n`, so the argument is circular.

**3.3 Dimension conservation under the compressor.**
- Restriction along `φ_A` conserves the total dimension, and the depth bound is monotone in dimension.
- Constituent dimension is not monotone under restriction, however. The quotient ring of a restricted
  constituent is related to the original only by containment, `J_κ ⊇ φ_A^(-1) J_ρ`, so `|B|` is not
  controlled.
- No depth drift beyond `k -> k/d` follows.

**3.4 Representation growth and averaging over finite quotients.**
- Landazuri–Seitz-type bounds are lower bounds on the degrees of nontrivial representations of congruence
  quotients.
- The only link from dimension to depth is the upper bound `D <= log_q(max constituent dimension)`.
- A lower bound on dimension agrees with the counterexample shape, which already needs doubly exponential
  dimension, so it cannot cap `D`.
- Averaging the rounding over the kernels of fixed finite quotients recovers only the bounded-depth mass of 3.2.

**3.5 Spectral gap at fixed generators.**
- The relative Kazhdan constant `κ` is a constant of the infinite pair, so it holds in every quotient. It is
  what makes each d-adic block cost `η_n`.
- The `log D` comes from the number of blocks, not from the cost per block.
- A rate-free bound would need a transport that acts on depth profiles through a non-amenable group. Only
  the compressor (`k -> k/d`) and the torus (`k -> k - 3`) exactify, and they generate a solvable drift
  (Attempts of `vertex-rounding-deep-nonunit-root-mass-vanishes`).

**3.6 Laurent extension.**
- A unit-type rounding factors through `St_r(R_+/I)` with every `x_i` invertible. So the quotient map
  extends to `F_q[x^(±1)] -> R_+/I`, and the rounding extends to `St_r(F_q[x^(±1)])`.
- It descends to `EL_r(F_q[x^(±1)])` only if the image of `K_2`, which includes symbols such as
  `{x_i, x_j}`, acts trivially.
- Nothing controls the extension against `σ` on the Laurent generators.
- So a unit-type rounding gives no input to `laurent-vertex-rounds-for-every-model`, and that claim gives no
  converse. Neither is used in §1.

## 4. What survives

- The target is the crux. Any progress on it is progress on
  `theorem-e-vertex-rounds-to-unit-type-representations`, and conversely.
- The cleanest open form is (c) for a single rounding family: vanishing deep non-unit mass.
- **Counterexample shape.** Deep origin mass spread log-uniformly over at least `c/η_n` d-adic blocks, with
  constituents of dimension doubly exponential in `1/δ_n^2`. No such model is known, and this lane built none.
