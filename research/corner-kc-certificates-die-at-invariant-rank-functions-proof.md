---
rg: 2
id: corner-kc-certificates-die-at-invariant-rank-functions-proof
kind: route
title: Read the commuting-conjugates relation entrywise, push the lamp into the compression gap, and average a rank function over the automorphism
target: corner-kc-certificates-die-at-invariant-rank-functions
requires:
  - minimal-subshift-algebra-is-simple-lef-ring
---

Notation is that of the claim. `E_ij` are the matrix units, `r E_ij` is `r` placed at `(i,j)`, and for
`r ∈ R`, `M_n(τ)` acts entrywise.

## 0. Preliminaries

**(P1) `U_f` is a group.** Put `F = f I_n`. An element `I + x` with `x = FxF` commutes with `F`, so its
inverse `I + y` in `GL_n(R)` commutes with `F` too. From `(1-F)(I+x) = 1-F` we get
`(1-F)(I+x)^-1 = 1-F`, so `(1-F)y = 0`, and symmetrically `y(1-F) = 0`. Hence `y = FyF ∈ M_n(fRf)`.

**(P2) Rank calculus.** A Sylvester matrix rank function satisfies `rk(1) = 1`,
`rk(AB) ≤ min(rk A, rk B)`, `rk(A ⊕ B) = rk A + rk B`, and the upper-triangular inequality. For
idempotents `g ≤ f` (meaning `g ∈ fRf`, equivalently `fg = gf = g`):
- `f - g` is an idempotent orthogonal to `g`;
- `rk(f) = rk(f-g) + rk(g)`. For `≤`, write `f = [1 1] diag(f-g, g) [1 1]^T`. For `≥`, write
  `diag(f-g, g) = [f-g ; g] · f · [f-g , g]`, a column times `f` times a row.
- `rk(a + b) ≤ rk(a) + rk(b)`, since `a + b = [1 1] diag(a,b) [1 1]^T`.
- `rk(h A h^-1) = rk(A)` for invertible scalar `h`, and also for permutation matrices, by two
  applications of `rk(AB) ≤ min`.

## 1. The gap inequality (CR1)

By assumption `Ad(u)(r E_pq) = τ(r) E_(π p, π q)` for all `r` and `p, q`.

**Compression.** `u e_ab(f) u^-1 = e_(πa,πb)(τ f) ∈ U_f`. So `τ(f) E_(πa,πb) ∈ M_n(fRf)`, which gives
`f' := τ(f) ∈ fRf`. Put `e' = τ(e)`. Then `e'` is an idempotent, and `e' f' = τ(ef) = 0 = f' e'`.

**The commuting pair.** Relabel `πi, πk, πj` as `1, 3, 2`; they are distinct. This is harmless,
because conjugation by a permutation matrix preserves `U_f` and matrix supports. Then:
- `u e_ik(e) u^-1 = I + P` with `P = e' E_13`;
- `u e_kj(e) u^-1 = I + e' E_32`.

Write `ℓ = I + x` and `ℓ^-1 = I + y`, where `x, y ∈ M_n(fRf)` by (P1). Put
`Q = (I+x) e' E_32 (I+y)`, so that `ℓ u e_kj(e) u^-1 ℓ^-1 = I + Q`. The hypothesis says that `I + P`
and `I + Q` commute, that is `PQ = QP`.

**Entries.** `Q_(pq) = (I+x)_(p3) e' (I+y)_(2q)`. Hence:
- `PQ = e' E_13 Q` is supported in row 1, with `(PQ)_(1q) = e' (1+x_33) e' (I+y)_(2q)`;
- `QP = Q e' E_13` is supported in column 3, with `(QP)_(p3) = (I+x)_(p3) e' y_21 e'`.

Compare the `(1,2)` entries. Column 2 is not column 3, so `(QP)_(12) = 0`, and

```text
(★)   e' (1 + x_33) e' (1 + y_22) = 0,        x_33, y_22 ∈ fRf.
```

**Push into the gap.** Expand (★):

```text
e' + e' x_33 e' + e' y_22 + e' x_33 e' y_22 = 0.
```

Right-multiply by `1 - f`. Since `y_22 (1-f) = 0`, this gives

```text
e'(1-f) = - e' x_33 e' (1-f) = - e' f x_33 e' (1-f),
```

using `x_33 = f x_33`. Therefore

```text
e' = e' f + e'(1-f) = e' f (1 + w),     w = - x_33 e' (1-f).
```

Finally, `e' f = e'(f - f') + e' f'`, and `e' f' = 0`. So `e' = e'(f - f')(1 + w)`.

**Rank.** `rk(e') ≤ rk(f - f') = rk(f) - rk(f')` by (P2), since `f' ≤ f`. This is (CR1). No property
of `L`, `C`, `D` beyond the displayed elements was used.

## 2. An invariant rank function (CR2)

**Compactness.** Let `𝒫(R)` be the set of Sylvester matrix rank functions, viewed as functions on
`⋃_(a,b) M_(a×b)(R)`. Each value satisfies `rk(A) = rk(A I_b) ≤ rk(I_b) = b`, and likewise `≤ a`. So
`𝒫(R)` sits in the product of the intervals `[0, min(a,b)]`, which is compact.

Each axiom is a closed condition that is preserved by convex combinations. The inequality
`rk(AB) ≤ min(rk A, rk B)` counts as two linear inequalities. So `𝒫(R)` is compact and convex.

**Averaging.** `σ` acts on `𝒫(R)` by `(σ·rk)(A) = rk(σ^-1(A))`. This map is affine and continuous, and
it maps `𝒫(R)` to itself. Fix `rk_0 ∈ 𝒫(R)` and put `rk_N = N^-1 Σ_(k<N) σ^k·rk_0`. Then

```text
(σ·rk_N - rk_N)(A) = N^-1 (σ^N·rk_0 - rk_0)(A),
```

which is bounded by `min(a,b)/N`. Any cluster point `ρ` of `(rk_N)` is therefore `σ`-fixed. This is the
Markov–Kakutani argument for one map.

**Invariance under every τ.**
- `ρ ∘ σ^m = ρ` for every `m ∈ Z`.
- `ρ(h_0 A h_0^-1) = ρ(A)` by (P2).
- So `ρ ∘ τ = ρ` for every `τ = Ad(h_0) ∘ σ^m`. One `ρ` serves every certificate.

**The null ideal.** Put `I_ρ = { r : ρ(r) = 0 }`.
- It is an additive subgroup, by `rk(a+b) ≤ rk(a) + rk(b)` and `rk(-a) = rk(a)`.
- It is a two-sided ideal, by `rk(s r s') ≤ rk(r)`.
- It is `σ`-invariant, and it is proper because `ρ(1) = 1`.

**Conclusion.** For a certificate, (CR1) gives

```text
ρ(e) = ρ(τ e) ≤ ρ(f) - ρ(τ f) = 0,
```

so `e ∈ I_ρ`, and then `eRe ⊆ I_ρ`. Any (KC) datum of corner form has `D ≤ [C,C] ≤ C ≤ U_e`, and
`U_e ⊆ I + M_n(I_ρ)`, so `D ≤ N_ρ`. Because `I_ρ` is a `σ`-invariant two-sided ideal, `N_ρ` is normal
in `GL_n(R) ⋊_σ Z`. So the normal closure in `G` lies in `G ∩ N_ρ`.

Finally, `e_12(r) ∈ N_ρ` if and only if `r ∈ I_ρ`, and `1 ∉ I_ρ`.

**Iteration.** Let `J ⊆ I_ρ` be `σ`-invariant. Then `ρ` factors through `R/J`, since
`ρ(A + B) ≤ ρ(A) + ρ(B)` for matrices and `ρ` vanishes on matrices over `J`. So `ρ` defines a
`σ`-invariant rank function `ρ̄` on `R/J` with `I_ρ̄ = I_ρ / J`. Applying the argument over `R/J`
gives certificates in `N_ρ̄`, and the preimage of `N_ρ̄` in `GL_n(R)` is `N_ρ`.

## 3. Simple targets (CR3)

Let `(u, e, f, ℓ)` be a certificate over `R`, and let `π_s : R → S_s` be one of the given maps, with
`π_s ∘ σ = σ_s ∘ π_s`.

**The image is a certificate.** Apply `π_s` entrywise and send `t ↦ t`. This is a homomorphism
`GL_n(R) ⋊_σ Z → GL_n(S_s) ⋊_(σ_s) Z`. Under it:
- `π_s(e)` and `π_s(f)` are orthogonal idempotents;
- `π_s(h_0)` is a unit;
- elements of `U_f` land in `U_(π_s f)`;
- the commutation relation is preserved.

So the image is a certificate over `S_s`.

**The corner vanishes.** By (CR2), `π_s(e) ∈ I_ρ` for a `σ_s`-invariant rank function `ρ` on `S_s`.
That ideal is proper and two-sided, and `S_s` is simple, so `I_ρ = 0` and `π_s(e) = 0`.

**Conclusion.** Joint injectivity gives `e = 0`. Then `U_e = {I}`, so `C` and `D` are trivial.

## 4. The subshift rings (CR4)

**Over `F_q`.** Let `R = LC(X,F_q) ⋊_T Z` with `X` an infinite minimal subshift. By
`minimal-subshift-algebra-is-simple-lef-ring`:
- `R` is simple (item 2);
- there is an injective unital ring homomorphism `R → prod_ω M_(N_k)(F_q)` (item 3).

The normalized rank `A ↦ lim_ω rank(A_k)/N_k` is a Sylvester matrix rank function on the
algebraic ultraproduct. Each axiom holds at every finite level and passes to the ultralimit. Its
pullback to `R` is a rank function with `rk(1) = 1`. Take the single map `π = id`, with `σ` arbitrary.

**Over `Z`.** Let `R_Z = LC(X,Z) ⋊_T Z`. Every element is a finite sum `Σ_j g_j u^j` with `g_j`
locally constant and integer-valued.
- `R_Z / pR_Z = LC(X,F_p) ⋊_T Z` is simple with a rank function, by the case above.
- Any ring automorphism `σ` of `R_Z` satisfies `σ(pR_Z) = pR_Z`, and so it induces `σ_p` on the
  quotient.
- An element in every `pR_Z` has all its coefficient functions divisible by every prime, hence zero.

So the reductions are jointly injective, and (CR3) applies.

This covers `σ` induced by any `ψ ∈ Aut(X,T)`, by `g ↦ g ∘ ψ^-1` and `u ↦ u`, since `ψ` commutes with `T`.
It also covers every other ring automorphism, including nonstandard ones.
