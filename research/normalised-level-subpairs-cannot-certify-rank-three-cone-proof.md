---
rg: 2
id: normalised-level-subpairs-cannot-certify-rank-three-cone-proof
kind: route
title: Read the span as a full matrix algebra over a coefficient ring, then cancel the level from outside by a commutator with a monomial unit, or through a finite-index ideal level, to reach the constant transvections
target: normalised-level-subpairs-cannot-certify-rank-three-cone
requires:
  - net-sandwich-level-subpairs-cannot-certify-rank-three-cone
  - subring-level-subpairs-cannot-certify-rank-three-cone
  - nonneg-generated-kazhdan-groups-have-nonsalient-cones
---

Proof of [[normalised-level-subpairs-cannot-certify-rank-three-cone]].  Notation as there.  Throughout
`e_ab(r) = 1 + r E_ab` for `a ≠ b`, and `[g, h] = g h g^-1 h^-1`.  We use the commutator formula

```text
[e_ac(r), e_cb(s)] = e_ab(r s)      (a, b, c distinct, r, s ∈ R),                     (CF)
```

and the fact that `U_k ⊇ { e_ab(x^m) : |m| ≥ k }`.

## (Z1) The coefficient ring

Assume `-e_l ∈ K0`.  By (Y1) of [[net-sandwich-level-subpairs-cannot-certify-rank-three-cone]], `Λ`
contains `I` and every `E_ab` with `a ≠ b`.  `Λ` is closed under products, because
`(g - 1)(h - 1) = (gh - 1) - (g - 1) - (h - 1)`.  So `E_aa = E_ab E_ba ∈ Λ`, and `M_3(F_q) ⊆ Λ`.

Put `A_B = { r ∈ R : r E_11 ∈ Λ }`.  It is an `F_q`-subspace, it contains `1`, and it is closed under
products, since `(r E_11)(s E_11) = rs E_11`.  For `X ∈ Λ`, `E_1a X E_b1 = X_ab E_11 ∈ Λ`, so `X_ab ∈ A_B`.
Conversely `r E_ab = E_a1 (r E_11) E_1b ∈ Λ` for `r ∈ A_B`.  Hence `Λ = M_3(A_B)`.

For `g ∈ E_B`, `g = 1 + (g - 1) ∈ M_3(A_B)`, and likewise `g^-1`.  So `g ∈ GL_3(A_B)`, with determinant `1`:
`E_B ≤ SL_3(A_B)`.

`B` normalises `E_B`, and `Ad(t)(g - 1) = t g t^-1 - 1`, so `Ad(t) Λ = Λ` for `t ∈ B`.  For `t = u σ` and a
scalar `r I`, `Ad(t)(r I) = u σ(r) u^-1 = σ(r) I`.  A scalar `r I` lies in `M_3(A_B)` iff `r ∈ A_B`.  So
`σ(A_B) ⊆ A_B` for `σ ∈ H_B`, and equality follows by applying this to `σ^-1`.

The proof of (Y1) produces `x^(-2kN e_l) I ∈ Λ`.  Also `x^(2kN e_l) I = Σ_a (x^(kN e_l) E_a b_a)(x^(kN e_l) E_(b_a) a)`
with `b_a ≠ a` lies in `Λ`, as `kN ≥ k`.  So `x^(± c e_l) ∈ A_B` with `c = 2kN`: a monomial unit.

*Pattern-sandwiched.*  Suppose `e_ab(σ_ab) ⊆ E_B ⊆ 1 + M(σ)`.  Then `Λ ⊆ M(σ)`, since `M(σ)` is linear, so
`A_B ⊆ σ_ab`, and `E_3(A_B) ≤ E_B`.  Conversely, if `E_3(A_B) ≤ E_B`, take `σ_ab = A_B` for all `a, b`:
`E_B ⊆ 1 + Λ = 1 + M_3(A_B)`.  This proves (Z1).

## (Z2) The unit commutator

Let `x^(-m) ∈ A'` with `m ∈ N^d \ {0}`, and let `E_3(A')` normalise `E_B`.  Choose `n ≥ 1` with `n|m| ≥ k`.
Put `t = x^(n m)`.  Then `t^-1 = (x^(-m))^n ∈ A'` and `e_ac(t) ∈ U_k ≤ E_B` for all `a ≠ c`.

Fix distinct `a, b, c` and `s ∈ A' ∪ {1}`.  Then `y = t^-1 s ∈ A'`, and `h = e_cb(y) ∈ E_3(A')` normalises
`E_B`.  With `g = e_ac(t) ∈ E_B`,

```text
[g, h] = g · (h g^-1 h^-1) ∈ E_B,        and by (CF)  [g, h] = e_ab(t · t^-1 s) = e_ab(s).
```

So `e_ab(1) ∈ E_B` and `e_ab(A') ⊆ E_B` for all `a ≠ b`, that is `E_3(A') ≤ E_B`.  No hypothesis on `K0` was
used.  ∎

## (Z3) Finite index

Let `x^(± m) ∈ A'`, `m ∈ N^d \ {0}`, so `1 = x^m x^(-m) ∈ A'`, and suppose `[E_3(A') : E_B ∩ E_3(A')] < ∞`.
Let `N_0` be the normal core of `E_B ∩ E_3(A')` in `E_3(A')`.  It is normal of finite index in `E_3(A')`.

*Entry sets.*  Put `K_ab = { r ∈ A' : e_ab(r) ∈ N_0 }`.  It is an additive subgroup, and its index in `A'` is at
most `[E_3(A') : N_0]`, because `r ↦ e_ab(r) N_0` is a homomorphism `A' → E_3(A') / N_0` with kernel `K_ab`.
For distinct `a, b, c`, `r ∈ K_ac` and `s ∈ A'`, (CF) and normality give `e_ab(rs) = [e_ac(r), e_cb(s)] ∈ N_0`.
Symmetrically, `r ∈ A'` and `s ∈ K_cb` give `rs ∈ K_ab`.  Hence

```text
K_ab ⊇ K_ac A'      and      K_ab ⊇ A' K_cb        (a, b, c distinct).
```

Put `𝔞 = K_12 A'`, the additive span of the products.  It is an ideal, and it contains `K_12` since `1 ∈ A'`.
The chain

```text
K_13 ⊇ K_12 A',  K_32 ⊇ A' K_12,  K_23 ⊇ A' K_13,  K_31 ⊇ K_32 A',  K_21 ⊇ K_23 A',  K_12 ⊇ K_13 A'
```

gives `𝔞 ⊆ K_ab` for every `a ≠ b`, using `A' A' = A'`.

*Unit.*  `𝔞 ⊇ K_12` has finite index, so `A'/𝔞` is a finite ring.  `t_0 = x^m` is a unit of `A'`, so its image
is a unit of the finite ring, and `t_0^n ≡ 1 mod 𝔞` for `n = |(A'/𝔞)^×|`.  Replace `n` by a multiple with
`n|m| ≥ k`.  Then `e_ab(t_0^n) ∈ U_k` and `1 - t_0^n ∈ 𝔞`, so

```text
e_ab(1) = e_ab(t_0^n) · e_ab(1 - t_0^n) ∈ U_k · N_0 ⊆ E_B .     ∎
```

## (Z4) Consequence

*Centraliser.*  In each case below `e_ab(1) ∈ E_B ∩ SL_3(R_+) = C`, so `E_3(F_p) = SL_3(F_p) ≤ C` and
`psi(C) ⊇ π(SL_3(F_p))`, where `π : SL_3(F_q) → F`.  Let `g ∈ SL_3(F_q)` centralise this image.  Then
`h ↦ g h g^-1 h^-1` is a homomorphism `SL_3(F_p) → μ_3`, which is trivial because `SL_3(F_p)` is perfect.
So `g` centralises `SL_3(F_p)`, which is absolutely irreducible, and `g` is scalar.  So `C_F(psi(C)) = 1`.

*Reduction to the cases.*  Let `B ⊇ U_k` be a Kun-Thom certificate: `B`, `C` Kazhdan, `C` infranormal and not
normal.  By (X2) of [[subring-level-subpairs-cannot-certify-rank-three-cone]], `H_B` is infinite.  By (X1)
there, `H_B` is generated by nonnegative matrices, and it is Kazhdan as a quotient of `B`.  By (W2) of
[[nonneg-generated-kazhdan-groups-have-nonsalient-cones]], `K0 ⊇ R^M` with `M ≠ ∅`, so `-e_l ∈ K0` for
`l ∈ M`, and (Z1) applies.

*Case 1: `E_B` normalised by `E_3(A_B)`.*  `A_B` contains `x^(-c e_l)`, so (Z2) applies with `A' = A_B`.

- *Normal in `GL_3(A_B)`.*  Immediate.
- *Conjugates.*  Let `E_B = D E_3(A) D^-1` with `D ∈ GL_3(Frac R)` and `A` a subring.  Then
  `Λ = D M_3(A) D^-1`, since the span of `E_3(A) - 1` is the algebra `M_3(A)`.  So `D M_3(A) D^-1 = M_3(A_B)`.
  Conjugation preserves centres, so `A = A_B`.  Thus `D` normalises `M_3(A_B)` and its unit group `GL_3(A_B)`.
  `E_3(A_B)` is normal in `GL_3(A_B)` by Suslin's normality theorem (`n = 3`, `A_B` commutative).  So `E_B` is
  normal in `D GL_3(A_B) D^-1 = GL_3(A_B)`.  No hypothesis on `Pic(A_B)` is used.
- *Subnormal.*  Let `B = B_0 ◁ B_1 ◁ .. ◁ B_r = B^+` with `E_3(A_(B^+)) ≤ E_(B^+)`.  Each `B_i ⊇ U_k`, and
  `K0(B^+) ⊇ K0(B)`, so `A^+ = A_(B^+)` has the monomial unit `x^(c e_l)` by (Z1).  `E_(B_(r-1))` is normalised by
  `B^+ ⊇ E_3(A^+)`, so (Z2) gives `E_3(A^+) ≤ E_(B_(r-1))`.  Descending, `E_3(A^+) ≤ E_(B_i)` for all `i`.

*Case 2: finite index.*  Let `B ≤ B'` with `[E_(B') : E_B] < ∞` and `E_3(A') ≤ E_(B')`, `A'` with a monomial
unit.  Then `[E_3(A') : E_B ∩ E_3(A')] ≤ [E_(B') : E_B] < ∞`, and (Z3) applies.  For a pattern-sandwiched,
net or subring `B'` ⊇ `B` of finite index, `E_(B') ⊇ E_3(A_(B'))` by (Z1), and `A_(B')` has a monomial unit
because `K0(B') ⊇ K0(B) ∋ -e_l`.  ∎

## Calibration checks

- `B = U_k`, `E_B = U_k ⊆ 1 + M_3(𝔪^k)`, so `e_ab(1) ∉ E_B`.  (Z2) predicts that no `e_cb(x^(-m))`,
  `m ∈ N^d \ {0}`, normalises `U_k`.  Directly: with `t = x^(nm)`, `n|m| ≥ k`, conjugating `e_ac(t) ∈ U_k` by
  `e_cb(x^(-nm))` gives `e_ab(-1) e_ac(t)` up to order, which is not in `1 + M_3(𝔪^k)`.
- `B` of finite index in `G` and containing `U_k`: (Z3) with `A' = R` gives `e_ab(1) ∈ E_B`, matching (V5) of
  [[twisted-diagonal-cones-need-a-profinitely-invisible-core]].
- The box-level net subpair (Y4) of the net node has a trace with nontrivial centraliser.  It contains no
  `U_k`, so none of (Z1)-(Z3) applies to it, consistently.

## Remark on the remaining class

Case 1 and Case 2 leave `E_B` that is thin in `SL_3(A_B)`: not normalised by `E_3(A_B)`, and meeting every
`E_3(A')` with a monomial unit in infinite index.  For `l ∈ M` and `s = x_l^c`, `c ≥ k`, the group
`Δ_l = E_B ∩ SL_3(F_q[s^(±1)])` contains `E_3(s F_q[s])`.  That group contains `E(F_q[s], s^2 F_q[s])`, by
the standard inclusion `E(n, A, I^2) ≤ E_n(I)`.  So it has finite index in `SL_3(F_q[s])`, since the relative group `SK_1(F_q[s], s^2 F_q[s])`
vanishes by Bass-Milnor-Serre.  (Z3) with `A' = F_q[s^(±1)]` forces `Δ_l` to have infinite index in
`SL_3(F_q[s^(±1)])`.  An intermediate-subgroup theorem of Venkataramana type for the `{0, ∞}`-arithmetic
group would force `Δ_l` to be bounded at `s = 0`, hence commensurable with a conjugate of `SL_3(F_q[s])`.  We
do not use or claim that theorem here.  It only indicates that the remaining class is the class of thin
overgroups of a level, and that the natural next tool is arithmeticity of such overgroups.
