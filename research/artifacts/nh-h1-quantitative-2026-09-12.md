# (H1) with a rate for the Theorem E vertex

Lane nh-h1-quantitative, 2026-09-12. Read at `19b046f71`, rechecked against `0879e0e43`.

## 1. Setting

- `R_+ = F_q[x_1..x_d]`, `L = F_q[x^(±1)]`, `z = x_1 ⋯ x_d`, `r, d >= 3`.
- `Γ = EL_r(R_+) < Δ = EL_r(L) < G = Δ ⋊ SL_d(Z)`, the explicit Theorem E pair plus its Laurent vertex `Δ`.
- `σ : G -> U(prod_U M_n)` is trace-preserving, and `π_n : Γ -> U(n')`, with `n'/n -> 1`, are (H1) roundings.
- `A ∈ SL_d(Z)` is a compressor with every entry `>= 1`. `δ_n` is the intertwining defect of a unitary
  representative of `σ_n(A)` between `π_n` and `π_n ∘ Ad A`, and `η_n = 4δ_n^2/κ^2`.
- `μ_n` is the normalized spectral measure of `f -> π_n(e_12(f))`. `P_n` projects onto the constituents
  trivial on `St_r(A_nu)`.
- `χ_nu` and `depth_nu` are as in `nonunit-component-root-mass-is-log-scale-folner`. `η_n^t` is as in
  `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`.

**Starting point.** Item 6 of the shallow claim gives

```text
τ(1 - P_n) <= r(r-1)[(q + 1 + log_d(r(r-1)n'))·η_n + η_n^t].
```

So unit type follows from `δ_n^2 log n -> 0`. The `log n` counts d-adic depth blocks up to the crude depth
bound `dim_(F_p) A_nu <= r(r-1)n'`.

## 2. Depth is logarithmic in dimension

**Lemma 2.1.** Let `B = R_+/I = A_u × A_nu` be finite and `π : St_r(B) -> U(N)`. Put
`J_χ = {b ∈ B : χ(bB) = 1}`. If `μ({χ}) > 0`, then

```text
q^(depth_nu(χ))  <=  |B/J_χ|  <=  dim V_χ  =  N·μ({χ}).
```

Here `V_χ` is the `χ`-eigenspace of `π(x_12(B))`. The middle inequality also holds inside every
irreducible constituent whose `x_12`-spectrum contains `χ`.

*Proof, first inequality.* Let `k = depth_nu(χ) >= 1`. Suppose `v = Σ_(i0 <= i < k) c_i e_nu z^i ∈ J_χ`, with
`c_(i0) ≠ 0`.
- Write `v = e_nu z^(i0) u` with `u = c_(i0) + z w`.
- Every local factor of `A_nu` has some `x_j` in its maximal ideal, which is nilpotent. So `z` is nilpotent on
  `A_nu`, and the `A_nu`-component of `u` is a unit.
- `J_χ` is an ideal, so `e_nu z^(i0) ∈ J_χ`. Hence `e_nu z^(k-1) B ⊆ J_χ ⊆ ker χ`.
- So `χ_nu` is trivial on `z^(k-1) R_+`, contradicting `depth_nu(χ) = k`.

The vectors `e_nu z^i`, `0 <= i < k`, are therefore independent in the `F_q`-space `B/J_χ`.

*Proof, second inequality.*
- `x_12` commutes with `x_13` and `x_32`, and `[x_13(b), x_32(c)] = x_12(bc)` (this uses `r >= 3`). So
  `X(b) = π(x_13(b))` and `Y(c) = π(x_32(c))` preserve `V_χ`, and `X(b)Y(c) = χ(bc)Y(c)X(b)` there.
- Take a joint eigenvector `v ∈ V_χ` of the commuting unitaries `X(B)`, with character `λ`. Then `Y(c)v` has joint
  character `b -> λ(b)χ(bc)`.
- Two such characters agree iff `c - c' ∈ J_χ`. The eigenspaces are orthogonal, so `dim V_χ >= |B/J_χ|`.

**Corollary 2.2.** `D(π) = max{depth_nu(χ) : μ({χ}) > 0}` is at most `log_q` of the largest dimension of an
irreducible constituent of `π`, hence at most `log_q N`. This is exponentially sharper than
`depth_nu <= r(r-1)N`. It is recorded as `root-character-nonunit-depth-at-most-log-q-dimension`.

## 3. The log-depth Følner bound

**Theorem 3.1.** With `D_n = D(π_n) <= log_q n'`:

```text
μ_n(depth_nu > 1)  <=  η_n (1 + log_d max(1, D_n)),
τ(1 - P_n)         <=  r(r-1)[(q + 1 + log_d max(1, D_n))·η_n + η_n^t].
```

*Proof.*
- Item 3 of `nonunit-component-root-mass-is-log-scale-folner` caps each block `d^j < depth_nu <= d^(j+1)` by `η_n`.
- Corollary 2.2 puts no mass above `D_n`. The blocks meeting `(1, D_n]` number `⌈log_d D_n⌉`.
- The projection bound (`nonunit-projection-bounded-by-root-spectral-mass`) and item 5 of the shallow claim
  give the second line.

**Corollary 3.2.** Under (H1), `δ_n^2 log(1 + D_n) -> 0` gives `τ(1 - P_n) -> 0`. In particular
`δ_n^2 log log n -> 0` suffices. This is recorded as `nonunit-root-mass-log-depth-scale-bound`.

## 4. The rate

- **Sufficient condition.** It is `δ_n^2 log(1 + D_n) -> 0`. The open claim `vertex-rounding-with-log-depth-rate`
  asks for (H1) with that rate, and the route `unit-type-rounding-via-log-depth-rate` feeds it into the crux.
- **Shape of a counterexample.**
  - Suppose `τ(1 - P_n) >= c > 0` along `U`.
  - The shallow term tends to 0, so `μ_n(depth_nu > 1) >= c/(r(r-1)) - o(1)`.
  - Theorem 3.1 then forces `⌈log_d D_n⌉ >= c'/η_n`, i.e. `D_n > d^(c'/η_n - 1)`.
  - By Lemma 2.1, some constituent has dimension at least `q^(D_n)`, doubly exponential in `1/δ_n^2`.
- **The intrinsic scale is `D_n`, not `n`.**
  - Amplifying `σ -> σ ⊗ 1_(m_n)` replaces `π_n` by `π_n ⊗ 1_(m_n)`.
  - That changes neither `δ_n` nor `μ_n` nor `D_n`, but it multiplies `n` arbitrarily.
  - So a rate stated in `n` can be destroyed without changing the conclusion.
- **Transport alone cannot produce the rate.** Compressors divide depth and the torus lowers it by 3, so the
  drift is amenable. A log-uniform profile on `[1, D]` passes every finite set of these tests once `log D`
  is large. See the Attempts of `vertex-rounding-deep-nonunit-root-mass-vanishes`
  (`nh-unit-type-valuations-2026-09-12.md`).

## 5. Which models (H1) must hold for

- **What the endgame consumes.** `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` applies the crux to
  `σ|G`, where `σ : W -> U(prod_U M_n)` witnesses hyperlinearity of `W = C_2 wr_(G/Γ) G`.
- **Two visible features of those models.**
  - `τ∘σ|G` is the regular trace.
  - The lamp `a_Γ` is a trace-zero symmetry in `σ(Γ)'`.
- **Neither constrains the root spectra of a rounding.**
  - Take any `σ` with rounding `π_n`. Take finite quotients `Q_k` of `G`, which is residually finite through
    `EL_r(F_q[(Z/N)^d]) ⋊ SL_d(Z/N)`, with `k = k(n) -> ∞` along `U`.
  - Then `σ ⊗ λ_(Q_k) ⊗ 1_2` has both features, and it has the rounding `π_n ⊗ λ_(Q_k)|Γ ⊗ 1_2` with the same
    defect on `F_Γ` and the same `δ_n`.
  - `λ_(Q_k)|Γ` is of unit type (Genuine actor models, crux Attempts), and a unit-type character has
    trivial non-unit component. So the non-unit mass `μ_n(χ_nu ≠ 1)` and `D_n` are unchanged.
- **So the restriction pays only through lamp covariance.** The one further structure is the covariant
  Bernoulli family `σ(g)a_(hΓ)σ(g)^* = a_(ghΓ)`. That is exactly what the endgame contradicts once
  normalization holds. Every statement about this model class holds vacuously if `W` is non-hyperlinear.
  A proof restricted to it must use the covariance, not just the existence of the models.

## 6. A rate-free alternative input: the Laurent vertex

**Lemma 6.1.** Let `ρ : Δ -> U(N)` be a finite-dimensional unitary representation. Then `ρ|Γ` factors through
`St_r(R_+/I)` for a finite-index ideal `I` in which every `x_i` is a unit. So `P = 1`.

*Proof.*
- `ρ(e_12(L))` is an elementary abelian `p`-subgroup of `U(N)`, so its kernel has finite index.
- Signed permutation matrices lie in `Δ`, and `[e_13(g), e_32(f)] = e_12(gf)`. So the kernel is an ideal
  `J ⊆ L`, the same for every root.
- Put `I = J ∩ R_+`, the root kernel of `ρ|Γ`. Item 1 of
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity` factors `ρ|Γ` through `St_r(R_+/I)`.
- `R_+/I` embeds in the finite ring `L/J`, where `x_i` is a unit. Its inverse is a positive power of `x_i`, so it
  lies in `R_+/I`.

**Consequence.** If `σ|Δ` rounds on a finite generating set `F_Δ` to genuine `ρ_n : Δ -> U(n')`, then
`π_n = ρ_n|Γ` rounds `σ|Γ` on `F_Γ`, because each `s ∈ F_Γ` is a fixed word in `F_Δ`. It is of unit type with
`P_n = 1`: no compressor transport, no torus, no rate.

This is the open claim `laurent-vertex-rounds-for-every-model`, with route
`unit-type-rounding-via-laurent-vertex-rounding`.
- `Δ` has property (T) by Ershov–Jaikin-Zapirain.
- `Δ` is infinite and residually finite, so it is not strictly HS-stable (Becker–Lubotzky arXiv:1809.00632).
- No converse is recorded. A unit-type rounding of `Γ` extends along `L -> A_u` only to `St_r(L)`, and nothing
  controls it on the Laurent generators `e_ij(x^(-a))`.

## 7. Status

- **Established here.**
  - Lemma 2.1 and Corollary 2.2, unconditional.
  - Theorem 3.1 and Corollary 3.2, under (H1).
  - Lemma 6.1.
- **Open.**
  - (H1) with the log-depth rate.
  - Laurent-vertex rounding.
  - Deep non-unit mass with no rate (sibling lane).
- **No explicit rate-violating model is known.** By §4 it would need constituents of dimension doubly
  exponential in `1/δ_n^2`, with non-unit mass spread log-uniformly over `>= 1/η_n` d-adic depth blocks.
