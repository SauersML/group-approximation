# Toms's Schubert algebra: common Cuntz lower bounds have a support gap, so (O6+) fails (2026-09-12)

Lane `ex-rank-problem-lix` (EX swarm). Target region: STW Problem XXIII, the Rank
Problem, on the concrete candidate `toms-schubert-algebra-misses-a-rank`.

**Outcome.**
1. **Theorem A.** In Toms's simple AH algebra `B` without uniform property Gamma,
   the equal-rank projections `p_m` and `q̂_m` (m large) have no common Cuntz lower
   bound that is uniformly tracially close to a projection of their common trace.
   The gap is at least `δ²/8`, where `δ` is Toms's survival constant.
2. **Corollary B.** No nonzero `c ≾ p_m, q̂_m` has a continuous rank function within
   `δ²/8` of `d(p_m)`. In particular none has `d(c) = d(p_m)`.
3. **Corollary C.** `Cu(B)` fails Thiel's axiom (O6+). Hence `B ⊗ K` does not have
   almost stable rank one, and Thiel's stable-rank-one proof that all ranks occur
   cannot run on `B`.

Nothing here decides whether all ranks occur in `B`. The obstruction is Toms's
(Thom–Porteous total degeneracy plus point-mass survival). The new content is the
passage from a common Cuntz lower bound with small support gap to an approximate
uniform-2-norm Murray–von Neumann equivalence, and the Cuntz-semigroup
consequences. Internal derivation, unreviewed.

## Sources and what was read

- A. S. Toms, *Schubert calculus and uniform property Γ*, arXiv:2606.12188v2
  (26 Jul 2026). MSI text copy
  `/projects/standard/hsiehph/sauer354/lit/toms-winter/2606.12188.txt`, lines
  40–460 and 905–1510 read in this lane. Used:
  - Section 4: `X_{i+1} = X_i × X_i × CP^{j_i}`, `j_i = 2d_i²`,
    `p_{i+1} = (π_1*p_i ⊗ γ_{i,1}) ⊕ (π_2*p_i ⊗ γ_{i,2})`, same for `q`;
    `rank p_i = rank q_i = d_i`; `p_1 = θ^d`, `q_1 = S` on `Gr(d,2d)`.
  - End of Section 5, verbatim: "By the Thom–Porteous obstruction, each pair
    (p_i, q_i) is therefore totally degeneracy-forcing. Equivalently, every bundle
    map p_i → q_i vanishes somewhere on X_i."
  - Proposition 4 (2)–(5) and its proof, and the proof of Theorem 5.
- H. Thiel, *Ranks of operators in simple C*-algebras with stable rank one*,
  Comm. Math. Phys. 377 (2020), arXiv:1711.04721v3. PDF pages 1–5, 9–11, 17–31
  read. Used: Paragraph 2.12 (Rørdam's lemma), Paragraph 2.14 (`d_τ`, `QT ↔ F(Cu)`),
  Theorem 4.7 (Edwards' condition for unital algebras), Definition 6.1 (O6+),
  Theorem 6.4, Remark 6.5, Example 6.7, Theorem 7.5, Remark 8.2, Lemma 8.3,
  Theorem 8.7, Theorem 8.11.

## 1. Setting and imported facts

`B = lim (B_i, ψ_i)`, `B_i = s_i (C(X_i) ⊗ K) s_i`, is Toms's Proposition 4 algebra.
`A_i = q_i (C(X_i) ⊗ K) q_i ⊂ B_i` is the old corner, `p_i ∈ M_k(A_i)`, and
`q̂_i = q_i ⊕ 0_{k−1} ∈ M_k(A_i)`. We identify stage elements with their images in
`M_k(B)`. `τ^{(k)} = τ ⊗ tr_k` is the normalized trace on `M_k(B)` for `τ ∈ T(B)`,
`τ ⊗ Tr` the unnormalized extension to `B ⊗ K`, and `‖z‖_{2,u} = sup_τ τ^{(k)}(z*z)^{1/2}`.

- **(T1) Total degeneracy (Toms, end of Section 5; relabelling in Section 7).** For
  every stage `n`, every `c ∈ q̂_n M_k(C(X_n) ⊗ K) p_n` vanishes at some `x ∈ X_n`.
- **(T2) Point-mass survival (Proposition 4(3)).** For every `n` and `x ∈ X_n` there is
  `τ_x ∈ T(B)` whose restriction to `B_n` is a measure `μ_x` with `μ_x({x}) ≥ δ`,
  where `δ = Π α_i > 1 − η > 0`.
- **(T3) Fibre trace (Proposition 4(4)).** `tr_{k,s_n}(p_n(x)) ≥ δ/k` for `x ∈ X_n`.
- **(T4) Topological branch (proof of Proposition 4(5)).** For `m < n` there is a
  projection `E = E_{n,m} ∈ M_k(B_n)` reducing `ψ_{n,m}(p_m)` and `ψ_{n,m}(q̂_m)`, with
  `E ψ_{n,m}(p_m) E = p_n`, `E ψ_{n,m}(q̂_m) E = q̂_n`, and
  `σ^{(k)}(1 − E) ≤ η_m := Σ_{r ≥ m} (1 − α_r)` for every trace `σ` on `B_n`.
  Also `Σ_i (1 − α_i) < ∞`, so `η_m → 0`.
- **(E) Equal ranks.** `p_m` and `q̂_m` have constant equal fibre rank, so
  `d_τ(p_m) = d_τ(q̂_m) = rank(p_m)/rank(s_m) =: ρ_m` for every `τ ∈ T(B)`.
- **(R) Rørdam's lemma (Thiel 2.12).** `a ≾ b` iff for every `ε > 0` there are `δ' > 0`
  and `x` with `(a − ε)_+ = xx*` and `x*x ∈ her((b − δ')_+)`. For a projection `b = p`,
  `her((p − δ')_+) = p(B ⊗ K)p`.
- **Standard functional calculus.**
  - (FC1) `x* F(xx*) x = (tF)(x*x)` for continuous `F`.
  - (FC2) `τ⊗Tr(g(xx*)) = τ⊗Tr(g(x*x))` for continuous `g ≥ 0` with `g(0) = 0` and
    `g(t)/t` bounded near `0`.
  - (FC3) On `C*(c)` a trace is integration against a Radon measure on
    `spec(c) \ {0}`, so `τ⊗Tr(f_j(c)) ↑ d_τ(c)` for continuous `f_j ↑ 1_{(0,∞)}` with
    `f_j(0) = 0`.

For `ε > 0` put `h_ε(t) = min(1, max(0, (t − ε)/ε))`. Then `h_ε ↑ 1_{(0,∞)}` as
`ε ↓ 0`, `h_ε ≥ h_{2ε}` and `h_ε² ≥ h_{2ε}`.

## 2. Theorem A

**Theorem A.** Let `m` satisfy `√η_m ≤ δ/(2√k)`. For every `c ∈ (B ⊗ K)_+` with
`c ≾ p_m` and `c ≾ q̂_m`, and every `ε > 0`,

```text
G_ε(c) := sup_{τ ∈ T(B)} ( d_τ(p_m) − τ⊗Tr(h_{2ε}(c)) )  ≥  δ²/8.
```

## 3. Proof

Suppose `G := G_ε(c) < δ²/8` for some `ε`. Put `a = (c − ε)_+` and
`g(t) = min(1, t/ε)`, so `h_ε(c) = g(a) =: e`.

**Step 1: two near projections under `p_m` and `q̂_m`.** By (R) applied to `c ≾ p_m`
there is `x` with `xx* = a` and `x*x ∈ p_m M_k(B) p_m`. Let
`g_2(t) = (g(t)/t)^{1/2}`, which is `ε^{−1/2}` on `[0, ε]` and `t^{−1/2}` beyond, and
put `x' = g_2(a) x`. By (FC1),

```text
x' x'* = g(a) = e,        z_P := x'* x' = g(x*x) ∈ p_m M_k(B) p_m,    0 ≤ z_P ≤ p_m.
```

By (FC2), `τ⊗Tr(z_P) = τ⊗Tr(e)` and `τ⊗Tr(z_P − z_P²) = τ⊗Tr(e − e²)`. Since `c ≾ p_m`,
`d_τ(c) ≤ d_τ(p_m)`. Using `h_ε ≥ h_{2ε}` and `h_ε² ≥ h_{2ε}`, for every `τ`:

```text
k τ^{(k)}(p_m − z_P)  = d_τ(p_m) − τ⊗Tr(h_ε(c))                  ≤ G,
k τ^{(k)}(z_P − z_P²) = τ⊗Tr(h_ε(c) − h_ε(c)²) ≤ d_τ(c) − τ⊗Tr(h_{2ε}(c)) ≤ G.
```

The same construction for `c ≾ q̂_m` gives `y'` with `y' y'* = e`,
`z_Q := y'* y' ∈ q̂_m M_k(B) q̂_m`, and the same two bounds.

**Step 2: approximate equivalence in uniform 2-norm.** Put `b := y'* x'`. Then
`b = q̂_m b p_m ∈ q̂_m M_k(B) p_m`, and

```text
b* b = x'* e x' = x'* x' x'* x' = z_P²,        b b* = y'* e y' = z_Q²,        ‖b‖ ≤ 1.
```

Since `0 ≤ p_m − z_P² ≤ p_m`, we have `(p_m − z_P²)² ≤ p_m − z_P²`, so

```text
‖p_m − b*b‖²_{2,u} ≤ sup_τ τ^{(k)}(p_m − z_P) + τ^{(k)}(z_P − z_P²) ≤ 2G/k =: β²,
```

and likewise for `q̂_m − bb*`. By `G < δ²/8`, `β < δ/(2√k)`.

**Step 3: compress to a late stage (Toms's estimate).** Fix `ν > 0`. Choose `n > m` and a
contraction `b_n ∈ M_k(B_n)` with `‖b − b_n‖ < ν`. Put

```text
c_n := q̂_n b_n p_n ∈ q̂_n M_k(C(X_n) ⊗ K) p_n.
```

By (T4), `p_n = p_n ψ(p_m) p_n`, and `R := ψ(q̂_m) − q̂_n = (1 − E)ψ(q̂_m)(1 − E)` is a
projection with `τ^{(k)}(R) ≤ η_m`. Since `b = ψ(q̂_m) b`, `b*b = b* ψ(q̂_m) b`, and

```text
p_n − c_n* c_n = p_n(ψ(p_m) − b*b)p_n
               + p_n(b* ψ(q̂_m) b − b_n* ψ(q̂_m) b_n)p_n
               + p_n b_n* R b_n p_n.
```

Using `‖uzw‖_{2,τ} ≤ ‖u‖ ‖z‖_{2,τ} ‖w‖`, `‖z‖_{2,τ} ≤ ‖z‖` and
`τ(z* R z) ≤ ‖z‖² τ(R)`, the three terms are bounded by `β`, `2ν` and `√η_m`:

```text
‖p_n − c_n* c_n‖_{2,u} ≤ β + 2ν + √η_m.
```

By (T1) there is `x ∈ X_n` with `c_n(x) = 0`, so `(p_n − c_n*c_n)(x) = p_n(x)`. Take
`τ_x` from (T2). Since `(p_n − c_n* c_n)²` is positive and equals `p_n(x)` at `x`, (T3)
gives

```text
‖p_n − c_n* c_n‖²_{2,u} ≥ ∫ tr_{k,s_n}((p_n − c_n*c_n)(y)²) dμ_x(y) ≥ μ_x({x}) · δ/k ≥ δ²/k.
```

Hence `δ/√k ≤ β + 2ν + √η_m` for every `ν > 0`. Letting `ν → 0` gives
`δ/√k ≤ β + √η_m < δ/(2√k) + δ/(2√k) = δ/√k`, where the strict inequality is
`β < δ/(2√k)` from Step 2. Contradiction. ∎

## 4. Corollaries

**Corollary B (continuous common lower bounds).** Let `m` be as in Theorem A and
`0 ≠ c ≾ p_m, q̂_m`. If `τ ↦ d_τ(c)` is continuous on `T(B)`, then
`sup_τ (d_τ(p_m) − d_τ(c)) ≥ δ²/8`. In particular no such `c` has `d(c) = d(p_m)`.

*Proof.* `F_ε(τ) := τ⊗Tr(h_{2ε}(c)) = τ⊗Tr(g'(x*x))` for the `x` of Step 1 and a
suitable `g'` with `g'(0) = 0` (FC2), with `x*x ∈ M_k(B)`. So `F_ε` is continuous on the
compact `T(B)` and increases to `d(c)` as `ε ↓ 0` (FC3). If `d(c)` is continuous, Dini's
theorem makes the convergence uniform, so
`G_ε(c) → sup_τ (d_τ(p_m) − d_τ(c))`, and Theorem A gives the bound. ∎

**Corollary C ((O6+) fails).** `Cu(B)` does not satisfy (O6+).

*Proof.* `Cu(B)` is countably based, simple and stably finite, satisfies (O5)
(Thiel, Proposition 2.13), `u = [1_B]` is compact and full, and Edwards' condition holds
for `∂_e K` (Thiel, Theorem 4.7, `B` unital). Here `K = F_{u↦1}(Cu(B)) ≅ QT(B) = T(B)`
(Thiel 2.14; `B` is nuclear). If (O6+) held, Thiel's Theorem 7.5 would give
`c ≤ [p_m], [q̂_m]` with `ĉ|_K = [p_m]^|_K ∧ [q̂_m]^|_K`. By (E) both functions equal the
constant `ρ_m`, so `d(c) = ρ_m = d(p_m)` is continuous, and `c ≠ 0` because `ρ_m ≥ δ > 0`.
This contradicts Corollary B. ∎

**Corollary D (almost stable rank one).** `B ⊗ K` does not have almost stable rank one.
In particular `sr(B) ≥ 2`.

*Proof.* Thiel's Theorem 6.4 gives (O6+) under stable rank one, and Remark 6.5 records
that the proof only needs `A ⊗ K` to have almost stable rank one. Apply Corollary C. ∎

This recovers `sr(B) ≥ 2`, which Toms obtained from Vaccaro's theorem, by a
Cuntz-semigroup route, and strengthens it to the stabilization.

**Corollary E (Thiel's architecture is closed on `B`).** Thiel proves Theorem 8.11 from
the standing hypotheses of his Section 8, which include (O6+). (O6+) enters through
Theorem 7.5, in Lemma 8.1 (Remark 8.2: "the assumption (O6+) is only used to realize
functional infima") and in Lemma 8.3. Theorem 8.7 then uses both. By Corollary C
these hypotheses fail for `B`, and Theorem A shows that the conclusion of Theorem 7.5
fails for the specific pair `([p_m], [q̂_m])`. So no proof that all ranks occur in `B`
can pass through attained functional infima below given elements.

## 5. What this says about the Rank Problem, and what it does not

- It does **not** show that some rank is unrealized in `B`. Theorem 7.5 asks for an
  infimum realized *below both* elements. Definition 7.1 (a rank equal to the
  infimum, anywhere) holds trivially for this pair.
- It isolates what a realizer of a continuous rank must avoid. By
  `all-ranks-occur-iff-continuous-ranks-are-dense`, every realizer of a strictly
  positive continuous affine function has continuous rank. Such an element lies
  within `δ²/8` of full trace below neither `p_m` nor `q̂_m`. The same rigidity holds
  for any pair of equal-rank bundles related by a nonzero top Thom–Porteous class at
  every stage.
- The negative mechanism in the Attempts of `toms-schubert-algebra-misses-a-rank`
  asks for a degeneracy class that survives the Cuntz supremum. Theorem A is exactly
  such a survival statement for the two-element meet: Toms's class survives
  `Cu`-level approximation because continuous ranks force uniform tracial support
  projections. What remains open is converting a realizer of a non-constant
  continuous `f` into a common lower bound of a totally degeneracy-forcing pair.
- Model test.
  - *A trivial model must fail the conclusion.* In a simple stable-rank-one algebra,
    Thiel's Theorem 7.5 applies. So every equal-rank pair of projections has a common
    lower bound `c` with `d(c)` equal to their rank, and by Dini its support gaps tend
    to `0`. The analogue of Theorem A fails there, as it must. The Jiang–Su algebra
    with `p = q = 1` is the smallest instance.
  - *The real object satisfies it.* `B` does, by Theorem A.
  - *Non-simple case.* In the non-simple Section 4 limit, the same proof with `δ = 1`
    and `η_m = 0` gives `G_ε(c) ≥ 1/8` for every `m`. Corollary C does not apply there,
    because Theorem 7.5 needs simplicity.

## 6. Novelty check (bounded)

Thiel's Examples 6.7 and 6.8 show (O6+) failing for `C(S²)`, which is not simple. One
web search on 2026-09-12 ("O6+" with simple C*-algebra) and Thiel's Section 6 located
no simple C*-algebra failing (O6+), and no statement that Toms's algebra fails it.
This is not a survey.
