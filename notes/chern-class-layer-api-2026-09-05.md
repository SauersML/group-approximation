# The Chern-class layer: construction decision and published API (2026-09-05)

Lane `found-chern-classes`, for the STW Problem LIX campaign (target 3 of
`notes/STW_THREE_TARGETS_PROGRAM_2026-09-05.md`).  Consumer:
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
Lemmas 2 and 3.

## 1. Construction decision, and why

**Rejected: define only the Chern classes of the campaign's explicit bundles.**
Lemma 3 quantifies over an *arbitrary* complex rank-`r` bundle `W` over
`S¹ × M` whose restriction to `{1} × M` is `V`.  A table of Chern classes for
explicit sums of tautological lines does not meet that quantifier.

**Rejected: replace the obstruction by a K-theoretic one.**  `F ⊕ 1 ≅ 1³`, so
`[F] = [1²]` in `K⁰`, so `[F ⊕ H] = [1² ⊕ H]`.  No additive K-invariant can
separate the two sides of Lemma 2.  The obstruction is genuinely unstable, and
genuinely cohomological.

**Rejected: Chern–Weil / de Rham.**  Mathlib at `81a5d257` has no de Rham
cohomology and no integration of differential forms over manifolds, so the
explicit curvature forms of the Grassmann connection of a projection-valued map
have nowhere to land.

**Rejected: an axiomatic `structure ChernTheory` whose fields are (a)–(f).**
That is a hypothesis smuggled into an endpoint, which the campaign forbids.

**Chosen: split the layer in two, and build the half that is cohomology-free,
completely and now.**

* **Layer 0 (this lane, unconditional, no topology).**  Total Chern classes as
  normalized formal power series over a commutative ring `A`, with `A` standing
  for the (as yet unbuilt) cohomology ring.  Whitney becomes the group
  multiplication and virtual classes become the group division, so those are
  true by construction rather than by axiom.  On top of that: Vieta, Newton, the
  square-zero step (2.7), the parity coefficient (2.8), the top-class
  computation (2.1), and the closing evenness inference of Lemma 3.
* **Layer 1 (blocked on `found-cohomology-ring` / `found-cpn-cohomology`).**
  `c(E)` for an arbitrary bundle, `c₁(L_j) = h_j`, the projective bundle formula
  and the splitting principle.  These need a cohomology ring with cup product;
  there is none in Mathlib at the pin, and the vendored
  `ThirdParty/HamSandwich/SphereOddDegree` tree still carries `sorry` in ten
  files (including every `RPnCupProduct*` module) and documents itself as pinned
  to Mathlib `v4.28.0`.

## 2. Published API — Layer 0

All in namespace `GroupApproximation.AlgTop`, `A` a `CommRing`.

### `GroupApproximation/AlgTop/ChernSeries.lean`

```lean
structure TotalChern (A : Type*) [CommRing A] where
  series : PowerSeries A
  constantCoeff_series : PowerSeries.constantCoeff series = 1

instance : CommGroup (TotalChern A)

def TotalChern.chernClass (c : TotalChern A) (k : ℕ) : A
def TotalChern.line (a : A) : TotalChern A          -- 1 + a X
def TotalChern.RankLE (c : TotalChern A) (n : ℕ) : Prop  -- c_k = 0 for k > n

theorem TotalChern.chernClass_zero (c : TotalChern A) : c.chernClass 0 = 1
theorem TotalChern.chernClass_mul (c d : TotalChern A) (n : ℕ) :        -- WHITNEY
    (c * d).chernClass n = ∑ p ∈ antidiagonal n, c.chernClass p.1 * d.chernClass p.2
theorem TotalChern.chernClass_line (a : A) (k : ℕ) :
    (line a).chernClass k = if k = 0 then 1 else if k = 1 then a else 0
theorem TotalChern.rankLE_line (a : A) : (line a).RankLE 1
theorem TotalChern.RankLE.mul  : c.RankLE m → d.RankLE n → (c * d).RankLE (m + n)
theorem TotalChern.RankLE.pow  : c.RankLE m → (c ^ d).RankLE (d * m)
theorem TotalChern.RankLE.prod : (∀ i ∈ s, (c i).RankLE (n i)) →
    (∏ i ∈ s, c i).RankLE (∑ i ∈ s, n i)
theorem TotalChern.chernClass_mul_top :
    c.RankLE m → d.RankLE n → (c * d).chernClass (m + n) = c.chernClass m * d.chernClass n
theorem TotalChern.chernClass_line_pow (a : A) (d : ℕ) : ((line a) ^ d).chernClass d = a ^ d
theorem TotalChern.chernClass_prod_top (s) (c) (n) : ...

-- the manuscript's (2.1), UNCONDITIONALLY (no nilpotence of the h j needed):
theorem TotalChern.chernClass_prod_line_pow_top (s : Finset ι) (h : ι → A) (d : ι → ℕ) :
    (∏ j ∈ s, (line (h j)) ^ (d j)).chernClass (∑ j ∈ s, d j) = ∏ j ∈ s, h j ^ d j

-- virtual classes: c(W) = c(V) · c(W / V) is the GROUP LAW
theorem TotalChern.mul_div_cancel_self (W V : TotalChern A) : V * (W / V) = W
theorem TotalChern.chernClass_eq_sum_div (W V : TotalChern A) (n : ℕ) : ...
```

### `GroupApproximation/AlgTop/ChernSplitNewton.lean`

```lean
theorem TotalChern.prod_series (s : Finset ι) (c : ι → TotalChern A) :
    (∏ i ∈ s, c i).series = ∏ i ∈ s, (c i).series
theorem TotalChern.chernClass_prod_line (s : Finset ι) (a : ι → A) (k : ℕ) :  -- VIETA
    (∏ i ∈ s, line (a i)).chernClass k = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i
theorem TotalChern.newton_of_split [Fintype ι] (a : ι → A) (k : ℕ) :          -- NEWTON
    (k : A) * (∏ i, line (a i)).chernClass k
      = (-1) ^ (k + 1) * ∑ q ∈ (antidiagonal k).filter (fun q => q.1 < k),
          (-1) ^ q.1 * (∏ i, line (a i)).chernClass q.1 * (∑ i, a i ^ q.2)
theorem TotalChern.natCast_mul_chernClass_of_split_squareZero : ...
```

### `GroupApproximation/AlgTop/ChernNewtonSquareZero.lean` — the manuscript's (2.7)

```lean
theorem natCast_mul_chern_eq_of_squareZero (c p : ℕ → A) (hc0 : c 0 = 1)
    (hnewton : ∀ k, 0 < k → (k : A) * c k = (-1) ^ (k + 1) *
      ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k), (-1) ^ a.1 * c a.1 * p a.2)
    (hsq : ∀ i j, 0 < i → 0 < j → c i * p j = 0) {k : ℕ} (hk : 0 < k) :
    (k : A) * c k = (-1) ^ (k + 1) * p k

theorem chern_eq_of_squareZero [Algebra ℚ A] (c ch : ℕ → A) ... :
    c k = (-1) ^ (k + 1) * ((k - 1)! : ℕ) * ch k
```

No logarithm and no exponential: Newton's identity plus `z² = 0` kills every
summand except `i = 0`, and `c₀ = 1`.

### `GroupApproximation/AlgTop/ChernParityCoefficient.lean` — the manuscript's (2.8)

```lean
theorem factorial_add_two_div_prod_factorial (s : Finset ι) (b : ι → ℕ) :
    ((∑ j ∈ s, b j) + 2)! / (∏ j ∈ s, (b j)!)
      = ((∑ j ∈ s, b j) + 2) * ((∑ j ∈ s, b j) + 1) * Nat.multinomial s b
theorem even_factorial_add_two_div_prod_factorial (s : Finset ι) (b : ι → ℕ) :
    Even (((∑ j ∈ s, b j) + 2)! / ∏ j ∈ s, (b j)!)
theorem two_dvd_chernCoefficient (s : Finset ι) (b : ι → ℕ) (a : ι → ℤ) (q : ℕ) :
    (2 : ℤ) ∣ (-1) ^ q * (((∑ j ∈ s, b j) + 2)! / ∏ j ∈ s, (b j)! : ℕ) * ∏ j ∈ s, a j ^ b j
```

The parity comes from the two consecutive integers `|b| + 1`, `|b| + 2`; the
multi-index plays no role.

### `GroupApproximation/AlgTop/ChernEvenTopClass.lean` — the close of Lemma 3

```lean
theorem TotalChern.chernClass_prod_line_pow_eq_zero_of_lt (s) (h) (d) :
    (∑ j ∈ s, d j) < k → (∏ j ∈ s, (line (h j)) ^ (d j)).chernClass k = 0
theorem TotalChern.two_dvd_chernClass_of_div (W V : TotalChern A) (r : ℕ) :
    V.chernClass r = 0 → (∀ j, 0 < j → (2 : A) ∣ (W / V).chernClass j) →
    (2 : A) ∣ W.chernClass r
```

Note the first: for `V = 1³ ⊕ H` with `H = ⨁_j L_j^{⊕d_j}`, the vanishing
`c_r(V) = 0` that the manuscript gets from `dim Y = 2m < 2r` is *already* a
consequence of `RankLE` — the total class of `V` is a product of `∑_j d_j` line
classes, hence a polynomial of that degree.  No dimension count is used.

## 3. What Layer 1 must supply, for whoever builds it

To finish Lemma 3 on top of this file set, the cohomology/K-theory lanes owe:

1. a commutative ring `A = H^{even}(S¹ × S⁵ × Y; ℚ)` (or ℤ, with the ℚ-algebra
   version used only for (2.7)) and the classes `t, x, h_j` in it, with
   `z = t x` satisfying `z ^ 2 = 0`;
2. a total Chern class `c : K⁰(Z) → TotalChern A` that is a group homomorphism
   from `(K⁰, +)` — Whitney — and is natural under pullback;
3. `c(L_j) = line h_j`, and `c(⨁_j L_j^{⊕d_j}) = ∏_j (line h_j) ^ d_j`, so that
   `chernClass_prod_line_pow_top` and
   `chernClass_prod_line_pow_eq_zero_of_lt` apply verbatim;
4. Newton's identity for `c` and `ch` on `K⁰` (the splitting principle), so that
   `natCast_mul_chern_eq_of_squareZero` applies to the virtual class `δ`;
5. `ch(δ) = z · ch(β)` for some `β ∈ K⁰(Y)` — the restriction sequence plus
   Künneth;
6. the top Chern number `⟨c_r(W), [S¹ × M]⟩` and its identification with the
   Euler number (`found-euler-class`).

Items 1, 3 and 5 are the ones with real content; 2 and 4 are consequences of the
splitting principle; 6 is a separate lane.
