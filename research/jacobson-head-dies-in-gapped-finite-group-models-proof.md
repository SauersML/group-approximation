---
rg: 2
id: jacobson-head-dies-in-gapped-finite-group-models-proof
kind: route
title: The gap turns a noncentral defect into global triviality, while central defects give a finite projective image of the finitely presented St_4(J), whose kernel contains x_12(Q), so the commutator x_13(Q) is linearly controlled by the defect
target: jacobson-head-dies-in-gapped-finite-group-models
requires:
  - fp-simple-groups-have-no-gapped-finite-unitary-models
  - lst-quasisimple-classical-character-ratio-bound
  - transvection-floor-kills-ambient-rank-transfers
  - cohn-elementary-group-is-not-lef
  - steinberg-finite-presentation-and-kazhdan-theorem
artifacts:
  - experiments/gapped-head-bound-2026-09-17/check_commutator_rigidity.py
---

Notation as on the target. All norms are normalized Hilbert-Schmidt norms. On unitaries they satisfy:
- `‖UA‖_2 = ‖AU‖_2 = ‖A‖_2` for unitary `U`;
- `‖U_1⋯U_m - 1‖_2 <= Σ ‖U_i - 1‖_2`.

For a representation `ρ` of `G` on `C^N`, `w^0` is the normalized dimension of the fixed space `(C^N)^G`.

## Step 1. Rigidity (R1): gap implies rigidity

Let `D` be noncentral and `λ ∈ U(1)`. Decompose `ρ = ⊕ m_χ χ`. The gap estimate in Step 2 of
`fp-simple-groups-have-no-gapped-finite-unitary-models-proof` is stated for `Re τ`. The same computation bounds the modulus:

```text
|tr ρ(D)| <= w^0 + Σ_{χ≠1} (m_χ χ(1)/N) |χ(D)|/χ(1) <= w^0 + θ(1 - w^0).
```

Hence

```text
‖ρ(D) - λ‖_2² = 2 - 2 Re(λ̄ tr ρ(D)) >= 2 - 2|tr ρ(D)| >= 2(1-θ)(1-w^0).
```

Every `ρ(y)` fixes `(C^N)^G` pointwise, so `‖ρ(y) - 1‖_2² <= 4(1 - w^0)` (Step 1 of the same route). Combining,
`‖ρ(y) - 1‖_2² <= (2/(1-θ)) ‖ρ(D) - λ‖_2²`, which is (R) with `C = sqrt(2/(1-θ))`.

For the classical family, (LST1) of `lst-quasisimple-classical-character-ratio-bound` gives `θ = 2^(-1/481)` for every
finite quasi-simple classical group. That family is therefore `C`-rigid with `C = sqrt(2/(1-2^(-1/481))) = 37.27...`.

## Step 2. Rigidity (R2) for GL_d(F_2), d >= 5, without Larsen-Shalev-Tiep

Here `GL_d(F_2) = SL_d(F_2)`, and the center is trivial, so "noncentral" means `≠ 1`.

**Lemma A (commutator step).** Let `E ∈ GL(V)`, `E ≠ 1`, and let `v ∈ Fix(E) ∖ Im(E - 1)`.
- `Im(E - 1) ≠ 0` does not lie in `span(v)`: if it did, it would equal `span(v)` and contain `v`.
  So there is a functional `φ` with `φ(v) = 0` and `φ|_{Im(E-1)} ≠ 0`.
- `E^(-1) - 1 = -E^(-1)(E - 1)`, and `E^(-1)` preserves `Im(E - 1)`. So `Im(E^(-1) - 1) = Im(E - 1)` and
  `β := φ∘(E^(-1) - 1) ≠ 0`.
- Put `x = 1 + v⊗φ` (that is, `x(w) = w + φ(w)v`). It is a transvection, since `φ(v) = 0`, and `x^(-1) = 1 - v⊗φ`.
- `Ev = v` gives `E x E^(-1) = 1 + v⊗φE^(-1)`.
- Since `φE^(-1)(v) = φ(v) = 0`,

```text
[E,x] = (1 + v⊗φE^(-1))(1 - v⊗φ) = 1 + v⊗β,        β(v) = 0,  β ≠ 0,
```

  a transvection.
- For every unitary representation `ρ` and every `λ ∈ U(1)`:

```text
‖ρ([E,x]) - 1‖_2 = ‖ρ(E)ρ(x) - ρ(x)ρ(E)‖_2
                 = ‖(ρ(E) - λ)ρ(x) - ρ(x)(ρ(E) - λ)‖_2 <= 2 ‖ρ(E) - λ‖_2.
```

**Two steps reach a transvection.** Let `D ≠ 1`.
1. Transvections generate `SL_d(F_2) = GL_d(F_2)`, and the center is trivial, so some transvection `x'` does not
   commute with `D`.
2. Put `E = [D,x'] = (Dx'D^(-1)) x'^(-1) ≠ 1`. It is a product of two transvections, so `rank(E - 1) <= 2`.
3. Then `dim Fix(E) >= d - 2 >= 3 > 2 >= dim Im(E - 1)` because `d >= 5`, so `Fix(E) ⊄ Im(E - 1)`, and Lemma A applies to `E`.

The result is a transvection `t = [E,x]` with

```text
‖ρ(t) - 1‖_2 <= 2 ‖ρ(E) - 1‖_2 <= 4 ‖ρ(D) - λ‖_2.
```

The first inequality is Lemma A with scalar `1`. The second is Lemma A's commutator estimate applied to `[D,x']`.

**Lemma B (transvection floor in HS form).** `t` is an involution, so `ρ(t)` has eigenvalues `±1`. Then
`‖ρ(t) - 1‖_2² = 4 rank(ρ(t) - 1)/N`.

Theorem 1 of `transvection-floor-kills-ambient-rank-transfers` (characteristic `0 ≠ 2`, `n = d >= 3`, `p = q = 2`,
`c(2,2) = 1/8`) gives `rank(ρ(t) - 1) >= (N - dim V^G)/8`. Hence `‖ρ(t) - 1‖_2² >= (1 - w^0)/2`.

With `‖ρ(y) - 1‖_2² <= 4(1 - w^0)`:

```text
‖ρ(y) - 1‖_2 <= 2√2 ‖ρ(t) - 1‖_2 <= 8√2 ‖ρ(D) - λ‖_2.
```

This is (R) with `C = 8√2`. The script in the artifact checks the Lemma A formula for random `D` in
`GL_d(F_2)`, `d = 5, 6, 7`. It also checks the inequalities on three permutation modules of `GL_5(F_2)`.

## Step 3. Theorem 1 (dichotomy)

Let `g, h ∈ F` and `q = φ(g)φ(h)φ(gh)^(-1)`. Right-multiply by the unitary `ρ(φ(gh))^(-1)` and divide by the scalar
`c(g)c(h)`:

```text
‖π(g)π(h) - π(gh)‖_2 = ‖ρ(q) - λ_{g,h}‖_2,        λ_{g,h} = c(gh)/(c(g)c(h)) ∈ U(1).
```

If (a) fails, some such `q` is noncentral. Then (R) gives, for every `y ∈ G`,
`‖ρ(y) - 1‖_2 <= C ‖ρ(q) - λ_{g,h}‖_2 <= C def_F(π)`, which is (b).

When `c ≡ 1`, we have `π(g) = ρ(φ(g))`. ∎

## Step 4. Corollary 1 (LEF)

Fix a finite `F ∋ 1` with `F = F^(-1)`. Put `F' = F ∪ FF`, and let
`η = min_{g ∈ F'∖{1}} liminf_k ‖π_k(g) - 1‖_2 > 0`.

(If `F' = {1}` there is nothing to prove.) For all large `k`, `‖π_k(g) - 1‖_2 > η/2` for every `g ∈ F'∖{1}`, and
`C def_{F'}(π_k) < η/2`.

- **Multiplicative.** Alternative (b) of Theorem 1 on `F'` would force `‖π_k(g) - 1‖_2 < η/2` for all `g`.
  So (a) holds. The centers are trivial, so `φ_k(g)φ_k(h) = φ_k(gh)` for all `g, h ∈ F'`.
- **Injective.** Suppose `g ≠ h` in `F` and `φ_k(g) = φ_k(h)`. Then `gh^(-1) ∈ F'∖{1}`, and exact multiplicativity on
  `F'` gives `φ_k(gh^(-1)) = φ_k(g)φ_k(h^(-1)) = φ_k(h)φ_k(h)^(-1) = 1`. Here `φ_k(h^(-1)) = φ_k(h)^(-1)`, from
  `φ_k(1) = φ_k(1)²`, which gives `φ_k(1) = 1`.
  - So `π_k(gh^(-1)) = 1`, which contradicts `η > 0`.

So `φ_k|_F` is an injective partial homomorphism into a finite group, and `Γ` is LEF. ∎

## Step 5. Theorem 2 (head bound)

Fix words over `X^±` (the letters of `X` and their inverses):
- a word for each relator `r ∈ R`;
- a word `u` for `μ`, and its formal inverse `u^(-1)`;
- a word for `ν`.

Write `a = ιμ`, `a' = ιμ^(-1)`, `b = ιν`, `b' = ιν^(-1)`, so that `ιλ = a b a' b'`. Let `F_1` consist of:
- `1`;
- `ι(x)` for `x ∈ X^±`;
- the `ι`-images of all prefixes of the relator words, of `u` and of `u^(-1)`;
- `b`, `b'`, `ab` and `aba'`.

Put `δ = def_{F_1}(π)`.

**Three elementary estimates.**
- (E1) `‖π(1) - 1‖_2 = ‖π(1)π(1) - π(1)‖_2 <= δ`.
- (E2) For `(g,h) = (a,a')` or `(b,b')`: `gh = 1`, so `‖π(g)π(h) - 1‖_2 <= 2δ`.
- (E3) Three multiplications along `(a,b)`, `(ab,a')` and `(aba',b')` give `‖π(ιλ) - π(a)π(b)π(a')π(b')‖_2 <= 3δ`.

**Central case: every defect on `F_1` is central (alternative (a)).** Write `φ̄ = φ mod Z(G)`, which takes values in
`G/Z(G)`.
- The pair `(1,1)` has defect `φ(1)`, so `φ̄(1) = 1`.
- The pairs `(ιx, ιx^(-1))` give `φ̄(ιx^(-1)) = φ̄(ιx)^(-1)`.
- Let `ψ : F(X) → G/Z(G)` be the homomorphism with `ψ(x) = φ̄(ιx)`.
- For a word `s_1⋯s_m` whose prefixes `p_i` have images in `F_1`, induction on the pairs `(ι p_(i-1), ι s_i)` gives
  `φ̄(ι p_i) = ψ(p_i)`.
- Every relator word `r` satisfies `ι(r) = 1`, so `ψ(r) = φ̄(1) = 1`. Thus `ψ` factors through a homomorphism
  `Λ → G/Z(G)` into a finite group.
- `μ` lies in the kernel of every homomorphism to a finite group, so `φ̄(a) = ψ(u) = 1` and `φ̄(a') = ψ(u^(-1)) = 1`.
  That is, `φ(a)` and `φ(a')` are central.
- Hence `π(a) = c(a)ρ(φ(a))` and `π(a')` commute with `π(b)`, and `π(a)π(b)π(a')π(b') = π(a)π(a') · π(b)π(b')`.
- By (E2), `‖π(a)π(a')π(b)π(b') - 1‖_2 <= ‖π(b)π(b') - 1‖_2 + ‖π(a)π(a') - 1‖_2 <= 4δ`.
- With (E3), `‖π(ιλ) - 1‖_2 <= 7δ`.

**Noncentral case (alternative (b)).** By Step 3, `‖ρ(y) - 1‖_2 <= s := Cδ` for every `y ∈ G`.
- If `c ≡ 1`, then `‖π(ιλ) - 1‖_2 = ‖ρ(φ(ιλ)) - 1‖_2 <= Cδ`.
- In general, write `π(a)π(b)π(a')π(b') = κ R` with:
  - `κ = c(a)c(a') · c(b)c(b')`;
  - `R = ρ(φa)ρ(φb)ρ(φa')ρ(φb')`, so that `‖R - 1‖_2 <= 4s`.
- `π(a)π(a') = c(a)c(a') ρ(φa)ρ(φa')`, and the `ρ` factor is within `2s` of `1`. With (E2),
  `|c(a)c(a') - 1| = ‖c(a)c(a')·1 - 1‖_2 <= 2δ + 2s`. The same holds for `b`, so `|κ - 1| <= 4δ + 4s`.
- Hence `‖κR - 1‖_2 <= ‖R - 1‖_2 + |κ - 1| <= 4δ + 8s`.
- With (E3), `‖π(ιλ) - 1‖_2 <= 7δ + 8Cδ`.

Both cases give the stated bounds, `(7 + 8C)δ` in general and `max(7, C)δ` when `c ≡ 1`. ∎

## Step 6. Corollary 2 (the Jacobson head)

**Finite presentation.** `J` is a finitely presented unital `F_2`-algebra, hence a finitely presented `Z`-algebra
(add `2 = 0`). So `St_4(J)` is finitely presented by `steinberg-finite-presentation-and-kazhdan-theorem`
(Krstić-McCool).

**`x_12(Q)` dies in every finite image of `St_4(J)`.** This is step 1 of `cohn-elementary-group-not-lef-proof`,
re-derived here from the Steinberg relations.
- `e_ab = S^a Q T^b` are matrix units: `TQ = QS = 0` and `TS = 1` give `e_ab e_cd = δ_bc e_ad`, with `e_00 = Q`.
- In a finite image `σ`, two of the `x_13(e_a0)` coincide, say for `a ≠ a'`. So `σ(x_13(r)) = 1` for `r = e_a0 + e_a'0`
  (characteristic `2`). Then:
  - `x_12(r) = [x_13(r), x_32(1)]` dies;
  - `x_32(e_0a r) = x_32(Q) = [x_31(e_0a), x_12(r)]` dies;
  - `x_12(Q) = [x_13(1), x_32(Q)]` dies.
- Also `[x_12(Q), x_23(1)] = x_13(Q)`.

Theorem 2 with `μ = x_12(Q)`, `ν = x_23(1)` then gives `‖π(z) - 1‖_2 <= (7 + 8C) def_{F_1}(π)`.

**Consequences.**
- For models with `def_F → 0` on finite sets, `‖π_k(z) - 1‖_2 → 0`.
- `2 - 2 Re tr π_k(z) = ‖π_k(z) - 1‖_2² → 0`, so every limit trace has `τ(z) = 1`.
- For a trace `τ`, `{g : τ(g) = 1}` is a normal subgroup, and `τ` is constant on its cosets (GNS). So `τ` factors
  through `Γ/<<z>>`.

**Instances of `ι`.**
- `St_4(J) → EL_4(J) ⊆ EL_n(J)`, `n >= 4`, by the upper-left corner.
- `J → L_2(F_2)`, `S ↦ s_2`, `T ↦ t_2`, is unital, since `t_2 s_2 = 1`. It sends `Q` to `1 - s_2 t_2 = s_1 t_1`, so
  `St_4(J) → St_4(L_2(F_2)) → St_20(L_2(F_2)) = Δ` sends `x_13(Q)` to `z = x_13(s_1 t_1)`.

**Calibration.** If `Γ` is residually finite, every `ι` kills `x_12(Q)`, and hence `z`. So a residually finite `Γ` with
gapped models, such as `SL_3(Z)`, never carries a nontrivial head from `St_4(J)`. Nothing contradicts the theorem. ∎

## Where each hypothesis enters

- **The gap.** Used once, in Step 3, to make a noncentral defect control every `ρ(y)`.
- **Finite presentation of `St_4(J)`.** Used once, in Step 5, to turn central defects on finitely many relators into a
  homomorphism.
- **The Steinberg chain.** Places `x_12(Q)` in the finite residual.
- **The commutator shape `z = [x_12(Q), x_23(1)]`.** Absorbs the central, possibly nonscalar, values `ρ(φ(a))`.
- **Not used.** Property (T), simplicity, and any structure of `φ` beyond its values on `F_1`.
