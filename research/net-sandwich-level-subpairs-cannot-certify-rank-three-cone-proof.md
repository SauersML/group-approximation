---
rg: 2
id: net-sandwich-level-subpairs-cannot-certify-rank-three-cone-proof
kind: route
title: Push level scalars through the projection to reach x^(-a) I, multiply back by a level unit to get every matrix unit in the span, and read the entry pattern to return to group elements
target: net-sandwich-level-subpairs-cannot-certify-rank-three-cone
requires:
  - subring-level-subpairs-cannot-certify-rank-three-cone
  - nonneg-generated-kazhdan-groups-have-nonsalient-cones
  - divisor-level-subpairs-cannot-certify-rank-three-twisted-cone
---

Notation as in [[net-sandwich-level-subpairs-cannot-certify-rank-three-cone]].  Throughout `B ≤ G` contains
`U_k`, `k ≥ 1`.

## Step 0. The span is an invariant algebra

`E_B = B ∩ EL_3(R)` is normal in `B`, since `EL_3(R)` is normal in `G`.  For `g, h ∈ E_B`,
`(g-1)(h-1) = (gh-1) - (g-1) - (h-1)`, so `Λ` is closed under products.  For `t ∈ B`,
`t(g-1)t^-1 = tgt^-1 - 1` with `tgt^-1 ∈ E_B`, so `Ad(t) Λ = Λ`.  Write `t = u σ`, `u ∈ EL_3(R)`,
`σ ∈ H_B` acting on `R` by `x^m ↦ x^(σm)`.  For a scalar `f`, `Ad(t)(f I) = u σ(f) u^-1 = σ(f) I`.

## Step 1. Level elements in the span

For `|m| ≥ k`, `e_ab(x^m) ∈ U_k ≤ E_B`, so `x^m E_ab ∈ Λ`.  Let `m ∈ N^d`, `|m| ≥ 2k`; split `m = m' + m''`
with `|m'|, |m''| ≥ k`.  For each `a` pick `b ≠ a`: `(x^(m') E_ab)(x^(m'') E_ba) = x^m E_aa ∈ Λ`.  Summing over
`a`, `x^m I ∈ Λ`.  By Step 0, `x^(σm) I ∈ Λ` for every `σ ∈ H_B`.

## Step 2. A negative coordinate direction gives x^(-a) I (proof of (Y1), first half)

`K0 = cone(H_B · R_+^d)` is the set of finite nonnegative real combinations of the vectors `h e_i`,
`h ∈ H_B`.  Suppose `-e_l ∈ K0`: `-e_l = Σ_s c_s h_s e_(i_s)` with `c_s ≥ 0` real, finitely many `s`.  The set
of `c ∈ R_(≥0)^S` solving this integral linear system is a nonempty rational polyhedron, so it has a rational
point.  Clearing denominators, `-N e_l = Σ_s n_s h_s e_(i_s)` with `N ≥ 1`, `n_s ∈ N`.  By Step 1 with
`m = 2k e_(i_s)`, `x^(2k h_s e_(i_s)) I ∈ Λ`.  Since `Λ` is an algebra,

```text
x^(-2kN e_l) I = Π_s ( x^(2k h_s e_(i_s)) I )^(n_s) ∈ Λ .
```

(If some `n_s = 0` drop it; not all vanish since `N ≥ 1`.)

## Step 3. Matrix units (proof of (Y1), second half)

`m = 2kN e_l` has `|m| = 2kN ≥ k`, so `x^m E_ab ∈ Λ` for `a ≠ b` by Step 1.  Hence
`E_ab = (x^(-m) I)(x^m E_ab) ∈ Λ` for all `a ≠ b`.  Also `I = (x^(-m) I)(x^m I) ∈ Λ` (as `|m| ≥ 2k`).  So `Λ`
contains `I` and every off-diagonal matrix unit, hence the algebra they generate, which is `M_3(F_q)`.  This
proves (Y1).  Only the single-variable level elements `e_ab(x_l^n)` and `x_l^(2kN)` were used from `U_k`.

## Step 4. Span to group (proof of (Y2))

Let `σ_ab` be a pattern for `E_B`.  Every `g ∈ E_B` has `g - 1 ∈ M(σ)`, and `M(σ)` is an `F_q`-linear
subspace of `M_3(R)`, so `Λ ⊆ M(σ)`.  The `(a,b)` coordinate of `E_ab ∈ Λ` is `1`, so `1 ∈ σ_ab` for every
`a ≠ b`.  Then `e_ab(1) ∈ e_ab(σ_ab) ⊆ E_B`, and `e_ab(1) ∈ SL_3(R_+) = Gamma`, so `e_ab(1) ∈ C`.  The
elements `ev_0(e_ab(1)) = e_ab(1)` generate `SL_3(F_q)`, so `psi(C) = F`.

*Examples of patterns.*  If `E_B = E(σ)` for a net `σ` (`σ_ab σ_bc ⊆ σ_ac` for all indices), then `M(σ)` is an
algebra containing `σ_ab E_ab`, so `1 + M(σ)` is closed under products and `E(σ) ⊆ 1 + M(σ)`.  Any group
between `E(σ)` and `G(σ) = SL_3(R) ∩ (1 + M(σ))` has the same pattern.  `EL_3(A)` has pattern `σ_ab = A`
(and diagonal `A`), recovering (X3) of [[subring-level-subpairs-cannot-certify-rank-three-cone]].

## Step 5. The consequence (Y3)

A Kun-Thom certificate has `B`, `C` Kazhdan, `C` infranormal and not normal, and `C_F(psi(C)) ≠ 1`.  By (X1)
of [[subring-level-subpairs-cannot-certify-rank-three-cone]], the nonnegative elements of `H_B` generate it;
`H_B = B / E_B` is Kazhdan.  If `H_B` is finite, (X2) there makes `C` normal.  If `H_B` is infinite, (W2) of
[[nonneg-generated-kazhdan-groups-have-nonsalient-cones]] (with `K0 = cone(H_B · O)`, not its closure) gives
`R^M ⊆ K0` with `M ≠ ∅`, so `-e_l ∈ K0`.  Steps 2–4 give `psi(C) = F`, which is centreless.  Either way `B`
is not a certificate.

## Step 6. The box-level example (Y4)

Variables `x = (x_1..x_(d_1))`, `y = (y_1, y_2)`, `d = d_1 + 2`, `d_1 ≥ 3`.  Put `S = F_q[x^(±1)][y_1, y_2]`,
`D = diag(1, 1, w)` with `w = y_1 y_2^(-1)`, and `B_0 = EL_3(S) x| SL_(d_1)(Z)`, with `SL_(d_1)(Z)` acting on
the exponents of `x` only.  `D ∈ GL_3(R)` normalises `EL_3(R)` (`D e_ab(f) D^-1 = e_ab(D_a D_b^-1 f)`), and
`D σ D^-1 = D σ(D)^-1 σ = σ` because `σ` fixes `y`.  So `B = D B_0 D^-1 = E(σ) x| SL_(d_1)(Z) ≤ G` with the net
`σ_ab = D_a D_b^-1 S`: `σ_ab = S` except `σ_13 = σ_23 = w^-1 S`, `σ_31 = σ_32 = w S`.

- *Kazhdan.*  `EL_3(S)` has (T) (Ershov-Jaikin-Zapirain, `S` finitely generated), `SL_(d_1)(Z)` has (T), and
  (T) is closed under extensions; `B ≅ B_0`.
- *Projection and cone.*  `H_B = SL_(d_1)(Z) x 1`, so `K0 = R^(d_1) x R_+^2 ∋ -e_1`, and `E_B = E(σ)`.
- *Levels.*  `e_ab(x^m y^n) ∈ B` whenever `n ≥ (1,1)`, since then `y^n ∈ σ_ab` for every pattern entry.  But
  `e_31(x_1^k) ∉ B`: every element of `E(σ) ⊆ 1 + M(σ)` has `(3,1)` entry in `w S`, whose monomials have
  `y`-exponent `(n_1 + 1, n_2 - 1)` with `n ∈ N^2`, and `x_1^k` has `y`-exponent `(0,0)`, which would need
  `n_1 = -1`.  So `B` contains a box level and no `U_k`.
- *Origin image.*  `C = B ∩ Gamma ⊆ E(σ) ∩ SL_3(R_+)` (an element `u σ` with `σ ≠ 1` is not in `Gamma`).  The
  monomials of `w^-1 S ∩ R_+` have `y`-exponent `(n_1 - 1, n_2 + 1)` with `n_1 ≥ 1`, so they are divisible by
  `y_2`; those of `w S ∩ R_+` are divisible by `y_1`.  So entries `(1,3), (2,3), (3,1), (3,2)` of every
  element of `C` vanish at `0`, and `psi(C)` lies in the image of `S(GL_2 x GL_1)(F_q)`.  For `λ ∈ F_q^*`
  with `λ^3 ≠ 1` (any `q ≥ 5`, or `q = 3`), `diag(λ, λ, λ^-2)` centralises it and is not scalar.
- *Edge not Kazhdan.*  `C ⊇ e_12(R_+), e_21(R_+)`.  Reduce modulo `J = (y_1, y_2, x_2, .., x_(d_1))`: the
  image lies in `S(GL_2 x GL_1)(F_q[x_1]) ≅ { g ∈ GL_2(F_q[x_1]) : det g ∈ F_q^* }` and contains
  `EL_2(F_q[x_1]) = SL_2(F_q[x_1])`, which has index dividing `q - 1`.  `SL_2(F_q[x_1])` acts on the
  Bruhat-Tits tree of `F_q((1/x_1))` without a fixed point (it is Nagao's nontrivial amalgam), so it lacks (T),
  and so does every group containing it with finite index.  So the quotient, and `C`, are not Kazhdan.
- *Where (Y1)-(Y2) break.*  Steps 0-2 hold for `B` with `U_k` replaced by the box level, but Step 3 needs a
  level element `x^m E_ab` with `m` a multiple of `e_l`, which the box level lacks.  Indeed `Λ ⊆ M(σ)`, and
  `1 ∉ σ_31`, so `E_31 ∉ Λ`.

So (Y2) is sharp in its level hypothesis, and this net subpair dies as a hypersurface-level subpair, as in
[[divisor-level-subpairs-cannot-certify-rank-three-twisted-cone]].
