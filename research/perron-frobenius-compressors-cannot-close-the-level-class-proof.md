---
rg: 2
id: perron-frobenius-compressors-cannot-close-the-level-class-proof
kind: route
target: perron-frobenius-compressors-cannot-close-the-level-class
requires:
  - level-groups-need-not-concentrate-on-monomial-lines
  - weight-bounded-level-subpairs-cannot-certify-rank-three
  - nonneg-generated-kazhdan-groups-have-nonsalient-cones
  - subring-level-subpairs-cannot-certify-rank-three-cone
  - monomial-origin-level-subpairs-cannot-certify-rank-three-cone
title: Proof that E_θ x| <σ>, θ the Perron eigenvector of σ^T, is a non-Kazhdan split subpair with every other certificate property and no line pole, that a primitive compressor makes the Newton cone of a survivor all of R^d, and that compressor twists are bounded
---

Notation as in [[perron-frobenius-compressors-cannot-close-the-level-class]].  Conventions: `G` acts on
`EL_3(R)` by `σ g σ^-1 = σ̂(g)`, where `σ̂(x^p) = x^(σ p)` entrywise; `v_w(Σ c_p x^p) = min { <w, p> : c_p ≠ 0 }`,
which is additive on products because the initial form of a product is the product of initial forms ((F1) of
[[level-groups-need-not-concentrate-on-monomial-lines-proof]]).  For a vector or matrix, `v_w` is the minimum
over entries; then `v_w(y z^T) = v_w(y) + v_w(z)` for column vectors `y, z`, since the minimum of
`v_w(y_i) + v_w(z_j)` over `i, j` is attained at the two separate minima.

## Step 0. Perron-Frobenius facts for nonnegative `σ ∈ SL_d(Z)`

Let `σ ≥ 0` be primitive, `σ^N > 0`, `d ≥ 2`.

- *(P0) `λ > 1`.*  `σ^N` has integer entries `≥ 1`, so `σ^N ≥ J` (all-ones matrix) entrywise and
  `ρ(σ)^N = ρ(σ^N) ≥ ρ(J) = d ≥ 2`.
- *(P1) `λ` is irrational.*  `λ` is a root of the monic integer polynomial `χ_σ`, whose constant term is
  `± det σ = ± 1`.  A rational root is an integer dividing `1`, so `λ = 1`, contradicting (P0).
- *(P2) Perron vectors.*  `σ` and `σ^T` are primitive, so there are `v, θ ∈ R^d_(>0)` with `σ v = λ v`,
  `σ^T θ = λ θ`, both unique up to scaling, and every other eigenvalue has modulus `< λ`.  The ray of `θ` is
  irrational: if `θ = c r` with `r ∈ Q^d`, then `λ = (σ^T r)_i / r_i ∈ Q`, contradicting (P1).
- *(P3) Forward orbits.*  Write `R^d = R v ⊕ V'` with `V' = θ^⊥`, which is `σ`-invariant because
  `<θ, σ y> = λ <θ, y>`.  The spectral radius of `σ|V'` is `< λ`.  So for `p ∈ R^d`,
  `σ^n p = (<θ, p>/<θ, v>) λ^n v + o(λ^n)`.  If `<θ, p> > 0`, then `σ^n p ∈ R^d_(>0)` for all large `n`.
- *(P4) Backward orbits of weights.*  For `w ∈ R^d_(≥0) \ 0`, `(σ^T)^N w > 0`, and `(σ^T)^n w / |(σ^T)^n w|`
  converges to `θ / |θ|` (apply (P3) to `σ^T`, whose Perron functional is `v`, with `<v, w> > 0`).

## Step 1. (Q1): the split subpair `B_σ = E_θ x| <σ>`

Recall from (Z3) of [[level-groups-need-not-concentrate-on-monomial-lines]]: `P_θ = { p ∈ Z^d : <θ, p> > 0 } ∪ 0`
is a monoid, `S_θ = F_q[P_θ]`, `I_θ ⊂ S_θ` is spanned by `x^p`, `p ∈ P_θ \ 0`, an ideal with `S_θ / I_θ = F_q`,
and `E_θ = E_3(S_θ, I_θ)` is the relative elementary group: the normal closure in `E_3(S_θ)` of the `e_ab(y)`,
`y ∈ I_θ`.  It lies in `SL_3(S_θ, I_θ) = { g ∈ SL_3(S_θ) : g ≡ 1 mod I_θ }`.

*`σ` normalises `E_θ`.*  `<θ, σ p> = <σ^T θ, p> = λ <θ, p>`, and `λ > 0`, so `σ(P_θ) ⊆ P_θ`; the same holds
for `σ^-1` (eigenvalue `λ^-1`).  So `σ̂` is an automorphism of `S_θ` preserving `I_θ`, hence of `E_3(S_θ)`
preserving `E_θ`.  Thus `B_σ = E_θ x| <σ>` is a subgroup of `G` (note `E_θ ≤ EL_3(R)`), `E_(B_σ) = E_θ`
(an element `g σ^n` with `n ≠ 0` has nontrivial projection) and `H_(B_σ) = <σ>`, infinite since `λ > 1`.

*Item 1.*  For `m ∈ N^d \ 0`, `<θ, m> > 0` since `θ > 0`, so `x^m ∈ I_θ` and `e_ab(c x^m) ∈ E_θ` for all
`c ∈ F_q`: `U_1 ≤ E_θ` in either coefficient convention.  `e_ab(1) ∉ SL_3(S_θ, I_θ)` since `1 ∉ I_θ`.  Next,
`C = B_σ ∩ Gamma = E_θ ∩ SL_3(R_+)`.  An element of `C` has entries in `S_θ ∩ R_+ = F_q[N^d]` congruent to
`δ_ij` modulo `I_θ ∩ R_+`, which is spanned by the `x^m`, `m ∈ N^d \ 0` (every such `m` lies in `P_θ \ 0`, and
the monomials of `R_+` in `I_θ` are exactly those).  So `ev_0(g) = 1` for `g ∈ C`: `psi(C) = 1` and
`C_F(psi(C)) = F ≠ 1`.

*Item 2.*  `σ ≥ 0` gives `σ(N^d) ⊆ N^d`, so `σ̂(R_+) ⊆ R_+` and `σ̂(SL_3(R_+)) ⊆ SL_3(R_+)`; together with
`σ̂(E_θ) = E_θ` this gives `σ C σ^-1 = σ̂(C) ⊆ C`, so `σ ∈ P_C`.  Also `C ⊆ P_C`.  Let `g ∈ E_θ`.  Its entries
involve finitely many exponents, all in `P_θ` (entries of elements of `SL_3(S_θ)` lie in `S_θ`).  By (P3),
there is `n` with `σ^n p ∈ N^d` for all of them (for `p = 0` trivially).  Then
`σ̂^n(g) ∈ SL_3(R_+) ∩ E_θ = C`, and `g = σ^-n σ̂^n(g) σ^n ∈ < C, σ >`.  So `< P_C > ⊇ < C, σ > = B_σ`: `C` is
infranormal.  It is not normal: `e_12(x_1) ∈ U_1 ≤ C`, and `σ^-1 e_12(x_1) σ = e_12(x^(σ^-1 e_1))`.  If
`σ^-1 e_1 ∈ N^d`, then `σ^-1 ≥ 0` on that column; if `σ^-1 ≥ 0` altogether, `σ` and `σ^-1` are nonnegative
integer matrices, so `σ` is a permutation matrix, which is not primitive for `d ≥ 2` (its powers are
permutation matrices).  So some column `σ^-1 e_i` has a negative entry, and `σ^-1 e_12(x_i) σ ∉ Gamma`.  For the
example, `σ^-1 e_1 = (0, 1, -1)`.

*Item 3* is the definition of `B_σ`.

*Item 4.*  Traces of `E_θ` lie in `S_θ`, so `N(E_θ) ⊆ P_θ`, and `σ(P_θ) = P_θ`.  A negative monomial ray point
`-j m`, `j ≥ 1`, `m ∈ N^d \ 0`, has `<θ, -j m> < 0`, so it is not in `P_θ`.  The first half (for every rational
`w ≠ 0` a trace monomial with `<w, p> < 0`) is (Z3.3) there: `w` is not a positive multiple of the irrational
ray of `θ` (P2), so the open cone `{ <θ, ·> > 0 > <w, ·> }` has a lattice point `p`, and
`e_12(x^p) e_21(x^p) ∈ E_θ` has trace `3 + x^(2p)`.

*Item 5.*  `E_θ` is normal in `B_σ`, so every conjugate of an element of `E_θ` by an element of `B_σ` lies in
`E_θ`.  A line section with `t = x^m`, `m ∈ N^d \ 0`: `S_θ ∩ F_q[t^(±1)] = F_q[t]`, since `x^(jm) ∈ P_θ` iff
`j ≥ 0`.  So `Δ_m ⊆ SL_3(F_q[t], t F_q[t])`, with pole order `0` at `t = 0`.

*Property (T) fails.*  `B_σ → <σ> ≅ Z` is onto.

*Why this refutes the step, and every single-compressor version of it.*  The step uses: `B ⊇ U_k`; a
nonnegative `σ ∈ H_B` of infinite order that is a compressor; trace monomials with `<w, p> < 0`; the
conjugates `u_n σ̂^n(g) u_n^-1 ∈ E_B`; and (L2).  All of this is present in `B_σ` (with `u_n = 1`), and the
conclusion (a line element with pole deeper than `2n`) is false.  Because the centraliser condition,
infranormality and non-normality hold too, the only hypothesis of a certificate that `B_σ` violates is
property (T), and the only consequence of (T) for `H_B` that the step can use without further input is that
`H_B` is not of the form `<σ>`.  More generally, for any subgroup `A ≤ SL_d(Z)` whose transpose fixes the
ray of some `θ ∈ R^d_(>0)` with positive eigenvalues, `E_θ x| A` is a subgroup of `G` with items 1, 4, 5,
by the same computation.  So an argument that closes the level class must use elements of `H_B` with no common
positive eigen-ray of their transposes, that is, the character-freeness that (W2) extracts from (T).

## Step 2. (Q2): a primitive compressor makes the Newton cone everything

Let `B ⊇ U_k` and `σ ∈ H_B` nonnegative and primitive.

*Invariance.*  For `b = u τ ∈ B` and `g ∈ E_B`, `b g b^-1 = u τ̂(g) u^-1 ∈ E_B` has trace `tr τ̂(g) = τ̂(tr g)`, whose
support is `τ(supp tr g)`.  Applying this to `b` and `b^-1` gives `τ N(E_B) = N(E_B)` for all `τ ∈ H_B`.  So
`Ncone(E_B)` is `H_B`-invariant, and `D = Ncone(E_B)^∨` is a closed convex cone with `τ^T D = D`.

*`D ⊆ O`.*  `e_12(x^m) e_21(x^m) ∈ U_k` for `|m| ≥ k` has trace `3 + x^(2m)`, so `2m ∈ N(E_B)` and
`Ncone(E_B) ⊇ O` (the cone of `{ m ∈ N^d : |m| ≥ k }` is `O`).  So `D ⊆ O^∨ = O`.  Also `Ncone(E_B) ⊇ τ O` for
`τ ∈ H_B`, so `Ncone(E_B) ⊇ K0` and `D ⊆ K0^∨`.

*Dichotomy.*  Suppose `D ≠ 0` and pick `w ∈ D \ 0`, so `w ≥ 0`.  The vectors `(σ^T)^n w / |(σ^T)^n w|` lie in
`D` and converge to `θ_σ / |θ_σ|` by (P4).  `D` is closed, so `θ_σ ∈ D`, that is `<θ_σ, p> ≥ 0` for every trace
monomial `p` of `E_B`.

*Survivors.*  If `± e_l ∈ K0` for some `l`, then every `w ∈ D ⊆ K0^∨` has `w_l = 0`.  `θ_σ` has
`(θ_σ)_l > 0`, so `θ_σ ∉ D`, hence `D = 0` and `Ncone(E_B) = D^∨ = R^d` (a closed convex cone is its double
dual).  By (Z1) of [[level-groups-need-not-concentrate-on-monomial-lines]], `W(E_B) = (D ∩ Q^d) \ 0 = ∅`.
For `EL_3(R)`, `N` contains `± 2m` for all `m`, so `Ncone = R^d` as well, and `e_ab(1) ∈ EL_3(R)`.  The
hypothesis `± e_l ∈ K0` holds for every survivor of (Y2) of
[[weight-bounded-level-subpairs-cannot-certify-rank-three]] ((W2) of
[[nonneg-generated-kazhdan-groups-have-nonsalient-cones]]: `K0 ⊇ R^M`, `M ≠ ∅`).

*Remark (what `D = 0` gives beyond (Y2)).*  (Y2) makes `E_B` unbounded at weights meeting `M`.  (Q2) makes it
unbounded at **every** nonzero rational weight, including weights supported off `M`, and puts trace monomials
in every open cone of directions.  For example, if `<θ_σ, p> < 0` for a trace monomial `p`, then (P3) gives
`σ^n p ∈ -R^d_(>0)` for large `n`: traces with monomials `x^(-q)`, `q ∈ N^d`, all `q_i` arbitrarily large.

## Step 3. (Q3): bounded twists

Let `c = u σ ∈ B` with `c C c^-1 ⊆ C` and `U_k ⊆ C`.  For `|m| ≥ k` and `a ≠ b`,
`c e_ab(x^m) c^-1 = u e_ab(x^(σ m)) u^-1 = 1 + x^(σ m) (u e_a)(e_b^T u^-1)`, using `u E_ab u^-1 = (u e_a)(e_b^T u^-1)`.
It lies in `C ⊆ SL_3(R_+)`, so `x^(σ m) (u e_a)(e_b^T u^-1) ∈ M_3(R_+)`.  For `w ∈ R^d_(≥0)` every nonzero
polynomial has `v_w ≥ 0`, so

```text
<w, σ m> + v_w(u e_a) + v_w(e_b^T u^-1) ≥ 0 .
```

Put `m = k e_i`: `<w, σ k e_i> = k (σ^T w)_i`.  Taking the best `i` gives (Q3).  (For `σ` with a zero row the
bound for that coordinate direction is `0`, and then `(u e_a)(e_b^T u^-1)` has no pole along that `x_l`.)

*Diagonal part.*  Replacing `u` by `u δ` with `δ = diag(x^(α_1), x^(α_2), x^(α_3))` changes `v_w(u e_a)` by
`<w, α_a>` and `v_w(e_b^T u^-1)` by `-<w, α_b>`.  The inequalities for `(a, b)` and `(b, a)` therefore bound
`<w, α_a - α_b>` from both sides once `u` is fixed; in this sense the diagonal part of the twist is bounded
linearly in `w`.  Nothing more is claimed: in particular (Q3) does not say that `u` itself can be chosen
polynomial.

## Step 4. (Q4): untwisted generators

Suppose `σ_1, .., σ_r ∈ B ∩ SL_d(Z)` generate `H_B`.  Then `B ⊇ < U_k, σ_1, .., σ_r > = B_(H_B, k)` in the notation of
[[monomial-origin-level-subpairs-cannot-certify-rank-three-cone]], and `C ⊇ C' = B_(H_B, k) ∩ Gamma`.  If `B`
is a certificate candidate with `H_B` infinite, Kazhdan and nonnegatively generated ((X1)), then (W2) gives a
line in `K0`, and (M2) gives `psi(C') = F`.  So `psi(C) = F`: the centraliser condition fails.  If `H_B` is
finite, (X2) of [[subring-level-subpairs-cannot-certify-rank-three-cone]] makes `C` normal.  For a
`Gamma`-conjugate `γ B γ^-1`, which has the same certificate status (`γ` normalises `Gamma`,
`psi(γ C γ^-1) = psi(γ) psi(C) psi(γ)^-1`), the level survives: with the convention `U_k = E_3(J_k)`,
`J_k = (x^m : |m| ≥ k)`, (F2) of [[level-groups-need-not-concentrate-on-monomial-lines-proof]] gives
`γ U_k γ^-1 ⊇ γ E_3(R_+, J_k^2) γ^-1 = E_3(R_+, J_k^2) ⊇ U_(2k)`.  So (Q4) applies to `γ B γ^-1` as well.

## Step 5. Checks

`experiments/pf-compressor-halfspace-2026-09-17/check_pf_halfspace.py` verifies, for
`σ = [[1,1,0],[0,1,1],[1,1,1]]`: `det σ = 1`, `σ ≥ 0`, `σ^2 > 0`; `χ_σ = x^3 - 3x^2 + 2x - 1` irreducible over
`Q`; `θ ≈ (0.5698, 1, 0.7549) > 0` with `σ^T θ = λ θ`, `λ ≈ 2.3247`; `σ` preserves the sign of `<θ, ·>` on the
box `[-6, 6]^3`; every `p ∈ P_θ` of the box reaches `N^3` within `5` steps of `σ`; negative monomial rays miss
`P_θ`; `σ^-1 e_1 = (0, 1, -1)`.  All checks pass (exit 0, `run.log`).  The script is a sanity check of the
example only; Steps 0-4 are the proof.
