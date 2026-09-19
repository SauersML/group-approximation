---
rg: 2
id: thompson-boundary-density-forms-are-extractable-proof
kind: route
title: "Brick normalization u_P = mu(P)^(-lambda) e_P turns invariance into a transport rule; transitivity on bricks, the two-children relation, and edge types pin every invariant form; the positive ones carry covariant PVMs, and the extractable class-kills finish"
target: thompson-boundary-density-forms-are-extractable
requires:
  - lifted-thompson-t-extractable-cocycles-bounded-on-centre
  - nv-extractable-cocycles-bounded-on-centralizers
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation as in the target.

**Imports.**
- (I1) Items 1-4 of `lifted-thompson-t-extractable-cocycles-bounded-on-centre`, and its example
  (a): a covariant projection-valued measure (PVM) on `S^1` gives a circle extraction.
- (I2) The Theorem and Corollaries 1-4 of `nv-extractable-cocycles-bounded-on-centralizers`.
- (I3) `T̄` is perfect, by item 2 of `lifted-thompson-t-perfect-centre-cubically-elliptic`.
- (I4) `nV` is simple. This is due to Brin: *Higher dimensional Thompson groups*, Geom. Dedicata
  108 (2004), for `n = 2`, and *On the baker's map and the simplicity of the higher dimensional
  Thompson groups nV*, Publ. Mat. 54 (2010), for all `n`. Cited from memory; not re-read at
  source.

## Part T̄

### Step 0. Brick vectors and the transport rule

For a brick `P` of length `2^{-k}` define:
- `e_P = Σ_{m ∈ Z} e(mθ) 1_{P+m}`, which lies in `D_θ`;
- `u_P = 2^{kλ} e_P`, which is `μ(P)^{-λ} e_P`.

These satisfy:
- **(R1) Translation.** `u_{P+m} = e(−mθ) u_P`.
- **(R2) Children.** Let `P0` and `P1` be the left and right halves of `P`. Then
  `u_P = 2^{-λ}(u_{P0} + u_{P1})`. This holds because `e_P = e_{P0} + e_{P1}` and
  `2^{kλ} = 2^{-λ} 2^{(k+1)λ}`.
- **(R3) Transport.** If `g ∈ T̄` is affine on `P` with slope `2^j` and `gP` is a brick, then
  `π_λ(g) u_P = u_{gP}`.
  - Proof: `(π_λ(g) 1_{P+m})(x) = 2^{-jλ} 1_{g(P+m)}(x)`, since `(g^{-1})' = 2^{-j}` on
    `gP + m`, and `g(P+m) = gP + m`.
  - So `π_λ(g) e_P = 2^{-jλ} e_{gP}`. Since `gP` has level `k − j`, this gives
    `π_λ(g) u_P = 2^{kλ − jλ} e_{gP} = u_{gP}`.
- **(R4) Spanning.** Every `F ∈ D_θ` that is constant on the bricks of level `k` equals
  `Σ_P F(p) 2^{-kλ} u_P`. The sum runs over the `2^k` level-`k` bricks `P = [p, p + 2^{-k})`
  contained in `[0,1)`. The formula follows from `1_{[0,1)} F = Σ_P F(p) 1_P` and
  quasi-periodicity.

Put `β(P,Q) = B(u_P, u_Q)`. By (R3), `β(gP, gQ) = β(P,Q)` whenever `g ∈ T̄` is affine on `P` and
on `Q` with brick images.

By (R4), and since every level-`k` vector is also a level-`(k+1)` vector, `B` is determined by
the numbers `β(P,Q)` with `P, Q ⊂ [0,1)` of a common level `k ≥ 1`. Two distinct such bricks
are *circle-disjoint*: `(P + Z) ∩ Q = ∅`.

### Step 1. Two transitivity lemmas

**(S) Subdivision.** Let `[x, y]` be an interval with dyadic endpoints and `x < y`. It is a union
of consecutive standard dyadic intervals, for example of length `2^{-N}` with
`x, y ∈ 2^{-N} Z`. Splitting one piece into its two halves raises the count by one. So for any
two such intervals there are standard subdivisions with the same number of pieces.

The piecewise-affine increasing map between two standard subdivisions with equal counts, which
maps each piece affinely onto the corresponding one, has slopes in `2^Z`, dyadic breakpoints,
and maps `Z[1/2]` to itself.

**Lemma T3.** Let `P = [p, p+ℓ)` and `P' = [p', p'+ℓ')` be bricks with `ℓ, ℓ' ≤ 1/2`. Then some
`g ∈ T̄` is affine on `P` with `gP = P'`.

*Proof.*
- Map `P` affinely onto `P'`.
- Map `[p+ℓ, p+1]` onto `[p'+ℓ', p'+1]` by (S). Both intervals have length at least `1/2`.
- Extend by `g(x + m) = g(x) + m`. This is continuous, since `g(p+1) = p'+1 = g(p) + 1`.
- The result is a homeomorphism of `R` with the defining properties of `T̄`. ∎

**Normalization.** Let `Q = [a, b)` be a brick and put `J_Q = [b, a+1)`. A brick `P` is
*normalized for `Q`* if `P ⊆ J_Q`. If `P` is circle-disjoint from `Q`, then exactly one
translate `P + m` is normalized for `Q`. By (R1), `β(P, Q) = e(mθ) β(P+m, Q)`.

A normalized `P = [p, p+ℓ) ≠ J_Q` has exactly one *type*:
- `L` if `p = b`;
- `R` if `p + ℓ = a + 1`;
- `I` otherwise.

Both equalities together would force `P = J_Q`.

**Lemma T1.** Let `P, P' ≠ J_Q` be normalized for `Q` and of the same type. Then some `g ∈ T̄`
fixes `[a, b]` pointwise, is affine on `P`, and satisfies `gP = P'`.

*Proof.*
- Take `g = id` on `[a, b]`.
- Map `[b, p]` onto `[b, p']` by (S). These are both degenerate or both nondegenerate, because
  the types agree. Map `P` affinely onto `P'`.
- Map `[p+ℓ, a+1]` onto `[p'+ℓ', a+1]` by (S), again both degenerate or both not.
- Extend 1-periodically. ∎

**Children and types.** Let `P = [p, p+ℓ) ≠ J_Q` be normalized, with children `P0, P1`. The
children are normalized and differ from `J_Q`. Their types are:
- type `I` → children `I, I`;
- type `L` → children `L, I`;
- type `R` → children `I, R`.

To check type `L`: `P0` starts at `b`, and its right end `p + ℓ/2` is less than `p + ℓ ≤ a+1`.
`P1` starts after `b`, and ends at `p + ℓ`, which is not `a + 1` since `P` is of type `L` only.
The other cases are the same.

### Step 2. Off-diagonal values

Fix a brick `Q` and write `B(u, u_Q)` as a function of `u`. By Lemma T1 and invariance, `β(P, Q)`
for normalized `P ≠ J_Q` depends only on the type of `P`. Call the three values
`φ_I(Q), φ_L(Q), φ_R(Q)`.

By (R2), `β(P,Q) = 2^{-λ}(β(P0,Q) + β(P1,Q))`, and by the table of children:
- (O_I) `φ_I = 2^{1−λ} φ_I`;
- (O_L) `φ_L = 2^{-λ}(φ_L + φ_I)`;
- (O_R) `φ_R = 2^{-λ}(φ_I + φ_R)`.

If `J_Q` itself is a brick, its children are `L` and `R`. So
`β(J_Q, Q) = 2^{-λ}(φ_L(Q) + φ_R(Q))`.

**Lemma T2.** If `λ ∉ Λ_0 ∪ Λ_1`, then `β(P, Q) = 0` for all circle-disjoint bricks `P, Q`.

*Proof.*
- `2^{1−λ} ≠ 1`, so (O_I) gives `φ_I = 0`.
- Then (O_L) reads `(1 − 2^{-λ}) φ_L = 0`, and `2^{-λ} ≠ 1`, so `φ_L = 0`. Likewise `φ_R = 0`.
- Hence `β(J_Q, Q) = 0` too.
- Normalization and (R1) cover every circle-disjoint `P`. ∎

### Step 3. Diagonal values; cases 1 and 2

Put `q(P) = β(P, P)`, which is real.
- **Constancy.** By Lemma T3 and invariance, `q(P) = c` for every brick of length at most `1/2`,
  for a single constant `c`.
- **The two-children identity.** Expanding `u_P` by (R2) in both slots gives, with
  `|2^{-λ}|² = 2^{-2 Re λ}`,

  (D) `q(P) = 2^{-2 Re λ} (q(P0) + q(P1) + β(P0,P1) + β(P1,P0))`.

**Cases 1 and 2** (`λ ∉ Λ_0 ∪ Λ_1`).
- By Lemma T2 the cross terms in (D) vanish, since `P0, P1` are circle-disjoint. For `ℓ ≤ 1/2`
  this gives `c = 2^{1 − 2Re λ} c`.
- If `Re λ ≠ 1/2`, then `c = 0`. By Lemma T2, `β` then vanishes on all pairs of level `k ≥ 1`,
  so `B = 0` by Step 0. This is case 1.
- If `Re λ = 1/2`, then for level-`k` bricks `P, Q ⊂ [0,1)`, `k ≥ 1`, we have
  `β(P,Q) = c δ_{PQ}`. Also
  `K_θ(u_P, u_Q) = δ_{PQ} |2^{kλ}|² 2^{-k} = δ_{PQ}`, because `e_P = 1_P` on `[0,1)`. So
  `B = c K_θ` by Step 0. This is case 2.
- Invariance of `K_θ` for `Re λ = 1/2`:
  - First, `|π_λ(g)F|² = (g^{-1})' |F∘g^{-1}|²`.
  - The function `|F|²` is 1-periodic, and `g^{-1}[0,1)` is an interval of length `1`.
  - So `∫_0^1 |π_λ(g)F|² = ∫_{g^{-1}[0,1)} |F|² = ∫_0^1 |F|²`. Polarize.

### Step 4. Case 3 (`λ ∈ Λ_1`, so `2^{-λ} = 1/2`)

**Off-diagonal.**
- (O_I) is empty. (O_L) and (O_R) give `φ_L = φ_R = φ_I =: φ(Q)`.
- `β(J_Q, Q) = φ(Q)` as well. So `β(P,Q) = φ(Q)` for every normalized `P`.
- *`φ` is constant.* Let `g ∈ T̄` be affine on `Q` with `gQ` a brick. Take `P` normalized for `Q`,
  of length `2^{-N}` with `N` large, starting at `b`. Then `g` is affine on `P` and `gP` is a
  brick. Since `g` is increasing and commutes with `z`, it maps `J_Q` onto `J_{gQ}`, so `gP` is
  normalized for `gQ`. Hence `φ(gQ) = β(gP, gQ) = β(P, Q) = φ(Q)`. By Lemma T3,
  `φ(Q) = κ` for all `Q` of length at most `1/2`.
- *Hermitian constraint.* Take `P = [p, p+ℓ)` normalized for `Q = [a,b)`, with `ℓ, |Q| ≤ 1/2`.
  Then `Q + 1 = [a+1, b+1) ⊆ [p+ℓ, p+1) = J_P`, so by (R1), `β(Q,P) = e(θ) β(Q+1, P) = e(θ) κ`.
  Hermitian symmetry gives

  (H1) `e(θ) κ = κ̄`, equivalently `κ = r e(−θ/2)` with `r ∈ R`.

**Diagonal.**
- `P1` is normalized for `P0`, so `β(P1, P0) = κ` and `β(P0, P1) = κ̄`.
- (D) with `Re λ = 1` gives `c = (2c + 2 Re κ)/4`, so `c = Re κ`.

**Conclusion.** Two invariant forms with the same `κ` agree on all level-`k` pairs, `k ≥ 1`, so
they are equal by Step 0. It remains to show that `B^1_θ` is invariant with `κ = e(−θ/2)`. Then
(H1) gives `B = r B^1_θ`.

**Invariance of `B^1_θ`.** For `λ ∈ Λ_1`, `π_λ = π_1`. Every `g ∈ T̄` factors as `g = ρ_t f`,
where `t = g(0) ∈ Z[1/2]`, `ρ_t(x) = x + t`, and `f = ρ_{−t} g` fixes `Z`. We may take
`t ∈ [0,1)` because `π_1(z)` is a unimodular scalar.
- *The factor `f`.* It maps `[0,1)` onto itself increasingly. Substituting `x = f(x')`,
  `y = f(y')` turns `B^1_θ(π_1(f)F, π_1(f)G)` into `∫∫ F(x')Ḡ(y') k_θ(fx', fy')`, and
  `k_θ(fx', fy') = k_θ(x', y')`.
- *The factor `ρ_t`.* Here `π_1(ρ_t)F = F(· − t)`. Substituting leaves the integral over
  `[−t, 1−t)²`. Move `x ∈ [−t, 0)` to `x + 1` using `F(x) = e(−θ)F(x+1)`, and likewise `y`. The
  kernel must then satisfy
  `e(−θ s_x) e(θ s_y) k_θ(x + t, y + t) = k_θ(x̃, ỹ)`, where `s_x = 1_{x<0}` and
  `x̃ = x + s_x`.
  - If `s_x = s_y`, the order is preserved and the phases cancel.
  - If `x < 0 ≤ y`: the left side is `e(−θ) e(θ/2) = e(−θ/2)`, and `x̃ > ỹ`, so the right side
    is `e(−θ/2)` too.
  - If `y < 0 ≤ x`: the left side is `e(θ) e(−θ/2) = e(θ/2)`, and `x̃ < ỹ`.
- *Its `κ`.* By rotation invariance, `B^1_θ` may be computed over the fundamental domain
  `[a, a+1)`. There `u_P = 1_P/μ(P)` and `u_Q = 1_Q/μ(Q)`, and `P` lies to the right of `Q`. So
  `β(P,Q) = e(−θ/2)`. ∎

(In Step 4, `gP` is a brick for large `N` because `g(b) ∈ 2^{j−N} Z` once `N` is large, where
`2^j` is the right slope of `g` at `b`.)

### Step 5. Case 4 (`λ ∈ Λ_0`, so `2^{-λ} = 1` and `u_P = e_P`)

**Off-diagonal.**
- (O_I) gives `φ_I = 2 φ_I`, so `φ_I = 0`. (O_L) and (O_R) are empty.
- *`φ_L` and `φ_R` are constant.* This is as in Step 4, using a small `L`-type `P` starting at
  `b`, and a small `R`-type `P` ending at `a+1`. So `φ_L ≡ ω_L` and `φ_R ≡ ω_R` on bricks `Q` of
  length at most `1/2`.
- *Hermitian constraint.* Take `P = [b, b+ℓ)` of type `L` for `Q = [a,b)`, with lengths at most
  `1/2`. Then `Q + 1` is normalized of type `R` for `P`. It ends at `b+1`, and it is not of type
  `L`, since `P` is not of type `R`. So `β(Q,P) = e(θ) ω_R`, and symmetry gives
  `ω_R = e(−θ) ω̄_L`.
- `β(J_Q, Q) = ω_L + ω_R`.

**Diagonal.** `P1` is normalized of type `L` for `P0`, and not of type `R` since `ℓ ≤ 1/2`. So
`β(P1,P0) = ω_L`, and (D) gives `c = 2c + 2 Re ω_L`, that is, `c = −2 Re ω_L`.

So an invariant form is determined by `ω_L =: γ ∈ C`.

**Realization.** `J_γ` is invariant, and its `ω_L` equals `γ`:
- *Well defined.* For `x ∈ Z[1/2]`, the summand at `x + 1` equals the one at `x`. The summand
  vanishes unless `F` or `G` jumps at `x`, because `M_γ (1,1)^T` is orthogonal to `(1,1)^T`. So
  the sum is finite and can be taken over any fundamental domain.
- *Invariant.* Since `g` is an increasing homeomorphism, `v_{F∘g^{-1}}(gx) = v_F(x)`, and
  `x ↦ gx` permutes `Z[1/2]` modulo `1`.
- *Its `ω_L`.* For `P = [b, b+ℓ)` of type `L` for `Q = [a,b)`, the only point where both
  `v_{e_P}` and `v_{e_Q}` are nonzero is `b` (mod 1). There `v_{e_P}(b) = (0,1)^T` and
  `v_{e_Q}(b) = (1,0)^T`, so `J_γ(e_P, e_Q) = (M_γ)_{12} = γ`. ∎

## Step 6. Positivity

- **Case 2.** `K_θ` is positive and nonzero, so `cK_θ ≥ 0` if and only if `c ≥ 0`.
- **Case 3, `θ ∈ Z`.** Here `k_θ ≡ e(θ/2) = ±1`, so `B^1_θ = e(θ/2) |m|²`.
- **Case 3, `θ ∉ Z`.**
  - Every `F ∈ D_θ` is determined by `F|_{[0,1)}`, and these restrictions are the dyadic step
    functions, which are dense in `L²[0,1)`. `B^1_θ` extends to a bounded form on `L²[0,1)`,
    because `|k_θ| = 1`.
  - Write `k_θ = cos πθ + i sin πθ · sgn(y − x)`. For `f` with `∫ f = 0` and `Φ(y) = ∫_0^y f`,
    we get `B^1_θ(f,f) = 2i sin πθ ∫_0^1 Φ f̄`.
  - For `f = e^{±2πix}` this equals `±sin(πθ)/π`, which takes both signs when `sin πθ ≠ 0`.
  - By density, some step functions give both signs. So `r B^1_θ ≥ 0` forces `r = 0`.
- **Case 4.**
  - Write `γ = −s + it`. Then `J_γ(F,F) = s Σ_x |F(x) − F(x−)|² − 2t Σ_x Im(conj F(x−) F(x))`.
  - Test with `N = 2^k`, `α = θ + k'` for `k' ∈ Z`, and `F = e(jα/N)` on `[j/N, (j+1)/N)`,
    `0 ≤ j < N`. This `F` extends to `D_θ` because `e(−θ) e((N−1)α/N) = e(−α/N)`.
  - The jump sum is `N |e(α/N) − 1|² = O(α²/N)`. The second sum is
    `−2tN sin(2πα/N) → −4πtα`.
  - Choosing `k'` so that `α` has either sign shows that `t = 0` is forced. Then `s ≥ 0` is
    forced by `F = e_P`, for which `J_γ(e_P, e_P) = 2s`. ∎

## Step 7. Corollaries A and A′

Let `B ≥ 0` be invariant, with null space `N_B`. Each `π_λ(g)` is bijective on `D_θ` and
preserves `B`, so it induces a unitary on `H_B`. We go through the cases.

- **Case 2** (`c > 0`). `H_B` is the closure of the step functions in `L²_θ`, which is all of
  `L²_θ`. The operators `π_λ(g)` extend to `ρ(g)f = (g^{-1})'^{1/2+it} f∘g^{-1}`.
  Multiplication `P(E)` by `1_{E+Z}`, for Borel `E ⊆ S^1`, is a PVM with
  `ρ(g) P(E) ρ(g)^{-1} = P(ḡE)`. This is example (a) of (I1).
- **Case 3** (`θ ∈ Z`, `r e(θ/2) > 0`). `H_B ≅ C` via `m`. We have
  `m(π_1(g)F) = ∫_{g^{-1}[0,1)} F = m(F)`, since `F` is periodic, so the representation is
  trivial.
- **Case 4** (`s > 0`). The map `F ↦ (F(x) − F(x−))_{x ∈ Z[1/2]}` sends `D_θ` isometrically, up to
  the factor `√s` and modulo `N_B`, into
  `ℓ²_θ(Z[1/2]) = {ξ : ξ(x+1) = e(θ)ξ(x), Σ_{x ∈ [0,1)} |ξ(x)|² < ∞}`. It intertwines `π_0`
  with `(σ(g)ξ)(x) = ξ(g^{-1}x)`, because `g^{-1}` is an increasing homeomorphism. Multiplication
  by `1_{E+Z}` is again a covariant PVM, and it restricts to the closed invariant image.

So every nontrivial `ρ_B` has a circle extraction.

**Corollary A′.** Split `ρ = ρ_0 ⊕ ρ_1`, where `ρ_0` collects the trivial summands and `ρ_1`
the extractable ones. Split `b = b_0 ⊕ b_1` accordingly.
- `b_0` is a homomorphism `T̄ → H_0`, so it is zero by (I3).
- By (I1) item 3, `ρ_1` is in the class `c ≥ 1/100`, and so is any representation weakly
  contained in `ρ_1`.
- By (I1) item 2, `sup_M ψ(z^M) = sup_M ‖b_1(z^M)‖² ≤ 400 Σ_i ψ(ĥ_i)`.

**Complementary series.** For `λ = 1/2 + s` with `s ∈ R` and `0 < |s| < 1/2`, we have
`λ ∉ Λ_0 ∪ Λ_1` and `Re λ ≠ 1/2`. So by case 1 there is no nonzero invariant form at all. ∎

## Part nV

### Step 8. Brick calculus on C^n

For a brick `P` put `u_P = μ(P)^{-λ} 1_P`, with `μ(P)^{-λ} = 2^{kλ}` when `μ(P) = 2^{-k}`. Let the
children `P0, P1` split the first coordinate word.
- **(R2′)** `u_P = 2^{-λ}(u_{P0} + u_{P1})`.
- **(R3′)** `π_λ(g) u_P = u_{gP}` whenever `g` is canonical on `P`, by the same computation as
  (R3).
- **(R4′)** `LC` is spanned by the `u_P`. Any two functions are combinations over one partition
  into bricks `[w_1] × ... × [w_n]` with all `|w_i| = k ≥ 1`. Such bricks are proper and
  pairwise disjoint.

**(S′) Subdivision.** A nonempty clopen set is a finite disjoint union of bricks. Splitting a
brick raises the count by one. So two nonempty clopen sets have brick partitions of equal size.

**Lemma N1.** Let `Q` be empty or a brick, and let `P, P'` be bricks disjoint from `Q` with
`P ∪ Q ≠ C^n` and `P' ∪ Q ≠ C^n`. Then some `g ∈ nV` is the identity on `Q` and canonical from
`P` onto `P'`.

*Proof.* Use (S′) to pair brick partitions of `C^n ∖ (P ∪ Q)` and `C^n ∖ (P' ∪ Q)`. Together
with `Q → Q` and `P → P'`, these define `g`. ∎

### Step 9. Theorem N

Let `β(P,Q) = B(u_P, u_Q)`.

**Off-diagonal.**
- Fix a brick `Q`. By Lemma N1, `β(P,Q) = φ(Q)` is the same for all bricks `P` disjoint from `Q`
  with `P ∪ Q ≠ C^n`.
- The children of such a `P` are again such bricks. So (R2′) gives `φ = 2^{1−λ} φ`.
- If `P ∪ Q = C^n`, then expanding `P` gives `β(P,Q) = 2^{1−λ} φ(Q)`.
- **So if `λ ∉ Λ_1`,** `β(P,Q) = 0` for all disjoint `P, Q`.
- **If `λ ∈ Λ_1`:**
  - `φ(gQ) = φ(Q)` for `g` canonical on `Q`. Take `P` small, so that `g` is canonical on it too.
  - Lemma N1 with `Q = ∅` shows that `nV` is transitive on proper bricks. So `φ ≡ κ`.
  - Hermitian symmetry gives `κ ∈ R`, and then `β(P,Q) = κ` also when `P ∪ Q = C^n`.

**Diagonal.**
- By Lemma N1 with `Q = ∅`, `q(P) = c` for all proper bricks `P`.
- Expanding by (R2′), with `P0 ∪ P1 = P` proper, gives
  `c = 2^{-2Re λ}(2c + β(P0,P1) + β(P1,P0))`.
  - For `λ ∉ Λ_1` this is `c = 2^{1−2Re λ} c`.
  - For `λ ∈ Λ_1` it is `c = (2c + 2κ)/4`, so `c = κ`.

**Conclusion by (R4′).**
- **`λ ∉ Λ_1`, `Re λ ≠ 1/2`.** Then `c = 0` and `B = 0`. This covers `λ ∈ Λ_0`, since then
  `Re λ = 0`.
- **`Re λ = 1/2`.** Then `β(P,Q) = c δ_{PQ}` on the partition. Also
  `∫ u_P ū_Q dμ = δ_{PQ} μ(P)^{1 − 2Re λ} = δ_{PQ}`. So `B = c ∫ F Ḡ dμ`.
- **`λ ∈ Λ_1`.** `β(P,Q) = κ` for all `P, Q` in the partition, including `P = Q`. Also
  `m(u_P) = 1`. So `B = κ m(F) conj m(G)`. ∎

### Step 10. Corollary N

Let `B ≥ 0`, so `c ≥ 0` or `κ ≥ 0`.
- **`Re λ = 1/2`.** `H_B = L²(C^n, μ)` with `ρ(g)f = J_{g^{-1}}^{1/2+it} f∘g^{-1}`.
  - Take `μ_r = (pr_j)_*(|r|² μ)` for each `j`. Then `|ρ(g)r|² = J_{g^{-1}} |r∘g^{-1}|²`, so the
    density `|ρ(g)r|² μ` is `g_*(|r|² μ)`.
  - Since `pr_j ∘ h^{(j)} = h ∘ pr_j`, this gives `μ_{ρ(h^{(j)}) r} = h_* μ_r` for every
    `h ∈ V`.
  - `μ_r(C) = ‖r‖²`.
  - `|μ_r(E) − μ_s(E)| = |‖1_{pr_j^{-1}E} r‖² − ‖1_{pr_j^{-1}E} s‖²| ≤ ‖r − s‖(‖r‖ + ‖s‖)`.
  - So `ρ` is coordinate-extractable.
- **`λ ∈ Λ_1`, `κ > 0`.** `H_B ≅ C` via `m`, and `m(π_1(g)F) = m(F)`, so the representation is
  trivial.

For a direct sum of such representations and a cocycle `b = b_0 ⊕ b_1`:
- `b_0` is a homomorphism `nV → H_0`, so it is zero by (I4).
- `b_1` goes into a direct sum of coordinate-extractable representations. By (I2) and the
  closure under direct sums, `ψ = ‖b_1‖²` satisfies the Theorem and Corollaries 1-4 of
  `nv-extractable-cocycles-bounded-on-centralizers`.

This gives the listed failures of properness, P1, P2, P3 and R1. ∎
