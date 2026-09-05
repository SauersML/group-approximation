# The Chern-class layer: construction decision and published API (2026-09-05)

Lane `found-chern-classes`, for the STW Problem LIX campaign (target 3 of
`notes/STW_THREE_TARGETS_PROGRAM_2026-09-05.md`).  Consumer:
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
Lemmas 2 and 3, and `GroupApproximation/AlgTop/MappingTorusParity.lean`.

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
cohomology and no integration of differential forms over manifolds.

**Rejected: an axiomatic `structure ChernTheory` whose fields are (a)–(f).**
That is a hypothesis smuggled into an endpoint.

**Chosen: encode a total Chern class as a normalized formal power series over
the (as yet unbuilt) cohomology ring, and build everything that is then pure
algebra — which turned out to include Newton's identity.**

The encoding is
```lean
structure TotalChern (A : Type*) [CommRing A] where
  series : PowerSeries A
  constantCoeff_series : PowerSeries.constantCoeff series = 1
```
with `c_k := coeff k series`.  Three consequences are structural rather than
axiomatic:

* **Whitney** `c(E ⊕ F) = c(E) c(F)` is the multiplication of `TotalChern A`.
* **Virtual classes.** `TotalChern A` is a `CommGroup` (a normalized series is a
  unit of `A⟦X⟧`), so `c(δ) = c(W) / c(V)` is *defined* and `c(W) = c(V) c(δ)`
  is the group law.
* **Newton's identity** is the degree-`q` coefficient of the logarithmic
  derivative identity `c · N(c) = X c'` with `N(c) = X c' / c`.  It therefore
  holds for **every** element of the group — virtual classes included — with no
  Chern roots, no `Fintype`, and no splitting principle.  This is the finding
  that matters: deriving Newton's identity is *not* topology in this encoding.

## 2. The API — all in `GroupApproximation.AlgTop`, `A` a `CommRing`

### `ChernSeries.lean` — GREEN (probe chern3)

```lean
structure TotalChern (A) [CommRing A]                     -- series, constantCoeff_series
instance : CommGroup (TotalChern A)
def TotalChern.chernClass (c : TotalChern A) (k : ℕ) : A
def TotalChern.line (a : A) : TotalChern A                -- 1 + a X
def TotalChern.RankLE (c : TotalChern A) (n : ℕ) : Prop   -- c_k = 0 for k > n

theorem TotalChern.chernClass_zero : c.chernClass 0 = 1
theorem TotalChern.chernClass_mul :                                        -- WHITNEY
    (c * d).chernClass n = ∑ p ∈ antidiagonal n, c.chernClass p.1 * d.chernClass p.2
theorem TotalChern.chernClass_line (a : A) (k : ℕ) :
    (line a).chernClass k = if k = 0 then 1 else if k = 1 then a else 0
theorem TotalChern.rankLE_line (a : A) : (line a).RankLE 1
theorem TotalChern.RankLE.mul / .pow / .prod / .mono
theorem TotalChern.chernClass_mul_top :
    c.RankLE m → d.RankLE n → (c * d).chernClass (m + n) = c.chernClass m * d.chernClass n
theorem TotalChern.chernClass_line_pow (a : A) (d : ℕ) : ((line a) ^ d).chernClass d = a ^ d
theorem TotalChern.chernClass_prod_top

-- the manuscript's (2.1), with NO nilpotence of the h j:
theorem TotalChern.chernClass_prod_line_pow_top (s : Finset ι) (h : ι → A) (d : ι → ℕ) :
    (∏ j ∈ s, (line (h j)) ^ (d j)).chernClass (∑ j ∈ s, d j) = ∏ j ∈ s, h j ^ d j

theorem TotalChern.mul_div_cancel_virtual (W V : TotalChern A) : V * (W / V) = W
theorem TotalChern.chernClass_eq_sum_div
```

### `ChernEvenTopClass.lean` — GREEN (probe chern3)

```lean
theorem TotalChern.chernClass_prod_line_pow_eq_zero_of_lt :
    (∑ j ∈ s, d j) < k → (∏ j ∈ s, (line (h j)) ^ (d j)).chernClass k = 0
theorem TotalChern.two_dvd_chernClass_mul
theorem TotalChern.two_dvd_chernClass_of_div (W V : TotalChern A) (r : ℕ) :
    V.chernClass r = 0 → (∀ j, 0 < j → (2 : A) ∣ (W / V).chernClass j) →
    (2 : A) ∣ W.chernClass r
```

The first is worth noting: for `V = 1³ ⊕ H` with `H = ⨁_j L_j^{⊕d_j}`, the
vanishing `c_r(V) = 0` that the manuscript derives from `dim Y = 2m < 2r` is
already a consequence of `RankLE` — the total class of `V` is a product of
`∑_j d_j` line classes, hence a polynomial of that degree.  No dimension count.

### `ChernSplitNewton.lean` — GREEN (probe chern3)

```lean
theorem TotalChern.prod_series
theorem TotalChern.chernClass_prod_line (s : Finset ι) (a : ι → A) (k : ℕ) :   -- VIETA
    (∏ i ∈ s, line (a i)).chernClass k = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i
theorem TotalChern.newton_of_split [Fintype ι] (a : ι → A) (k : ℕ)             -- via Mathlib
```

### `ChernSquareZeroIdeal.lean` — GREEN (probe chern3)

```lean
theorem mul_eq_zero_of_mem_squareZero {z a b : A} (hz : z * z = 0) : z * a * (z * b) = 0
theorem squareZero_of_dvd_squareZero (c p : ℕ → A) {z : A} (hz : z * z = 0)
    (hc : ∀ i, 0 < i → z ∣ c i) (hp : ∀ j, 0 < j → z ∣ p j) :
    ∀ i j, 0 < i → 0 < j → c i * p j = 0
```

### `ChernPowerSums.lean` — the Newton discharge

```lean
def TotalChern.newtonSeries (c : TotalChern A) : PowerSeries A      -- X c' / c
def TotalChern.powerSum (c : TotalChern A) (q : ℕ) : A              -- (-1)^(q+1) coeff q (N c)

theorem TotalChern.series_mul_newtonSeries : c.series * newtonSeries c = X * c.series'
theorem TotalChern.newtonSeries_mul : newtonSeries (c * d) = newtonSeries c + newtonSeries d
theorem TotalChern.powerSum_mul : (c * d).powerSum q = c.powerSum q + d.powerSum q
theorem TotalChern.powerSum_div : (W / V).powerSum q = W.powerSum q - V.powerSum q
theorem TotalChern.natCast_mul_chernClass (c : TotalChern A) (q : ℕ) :      -- NEWTON
    (q : A) * c.chernClass q
      = ∑ ij ∈ antidiagonal q, c.chernClass ij.1 * ((-1) ^ (ij.2 + 1) * c.powerSum ij.2)
theorem TotalChern.natCast_mul_chernClass_of_squareZero
```

### `ChernLineRoots.lean` — the identification

```lean
theorem TotalChern.powerSum_line (a : A) {q : ℕ} (hq : 0 < q) : (line a).powerSum q = a ^ q
```

so on a split class `p_q = ∑ᵢ aᵢ^q` and `chernChar` is the classical
`ch = ∑ᵢ exp(aᵢ)`.

### `ChernNewtonIdentity.lean` — `[Algebra ℚ A]`

```lean
def TotalChern.chernChar (c : TotalChern A) (q : ℕ) : A := ((q ! : ℚ)⁻¹) • c.powerSum q
theorem TotalChern.factorial_mul_chernChar : ((q ! : ℕ) : A) * c.chernChar q = c.powerSum q
theorem TotalChern.chernChar_mul / chernChar_div          -- ch is additive
theorem TotalChern.newton_identity_range (c : TotalChern A) (q : ℕ) (hq : 0 < q) :
    (∑ i ∈ Finset.range q,
        (-1 : A) ^ i * c.chernClass i * (((q - i)! : ℕ) : A) * c.chernChar (q - i))
      + (-1 : A) ^ q * (q : A) * c.chernClass q = 0
```

That last is the `newton` field of the parity chain's Newton hypothesis,
verbatim.

### `ChernNewtonDischarge.lean` — the payoff, `[Algebra ℚ A]`

```lean
theorem isUnit_natCast_pos {k : ℕ} (hk : 0 < k) : IsUnit ((k : ℕ) : A)
theorem TotalChern.chernClass_eq_of_chernChar_sq_zero (c : TotalChern A)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j → c.chernChar i * c.chernChar j = 0) :
    ∀ q : ℕ, 0 < q →
      c.chernClass q = (-1 : A) ^ (q + 1) * ((((q - 1)! : ℕ) : A) * c.chernChar q)
```

This is `hshift` of `MappingTorusParity.two_dvd_chernClass_of_parity`, with **no
Newton hypothesis** — only the square-zero condition that `z² = 0` supplies.

### `ChernMap.lean` — naturality in the coefficient ring

```lean
def TotalChern.map (f : A →+* B) : TotalChern A →* TotalChern B
theorem TotalChern.chernClass_map / map_line / RankLE.map / powerSum_map
```

Because `map f` is a monoid hom of groups it commutes with `⁻¹` and `/`, so a
virtual class transports for free.  This is the `ι : S →+* R` of the parity
chain's integral-to-rational comparison.

## 3. What the topological lanes still owe

To finish Lemma 3 on top of this file set:

1. a commutative ring `A = H^{even}(S¹ × S⁵ × Y)` with the classes `t, x, h_j`,
   and `z = t x` with `z ^ 2 = 0`;
2. a total Chern class `c : K⁰(Z) → TotalChern A`, a group homomorphism from
   `(K⁰, +)` and natural under pullback;
3. `c(L_j) = line h_j`, so that `chernClass_prod_line_pow_top` and
   `chernClass_prod_line_pow_eq_zero_of_lt` apply verbatim;
4. `ch(δ) = z · ch(β)` for some `β ∈ K⁰(Y)` — restriction sequence plus Künneth;
5. the top Chern number `⟨c_r(W), [S¹ × M]⟩` and the Euler-class identification.

Item 4 is what feeds `hsq`; `ChernSquareZeroIdeal.squareZero_of_dvd_squareZero`
turns `z ∣ ch_q(δ)` and `z² = 0` into it.  Newton's identity is **no longer** on
this list.

## 3a. The exact join with `found-cohomology-ring`, as of 16:30

`TotalChern A` wants ONE commutative ring `A`.  What
`GroupApproximation/AlgTop/{SingularCohomology,CupProduct,CupAssoc,CrossProduct}.lean`
currently provide is the *graded* picture:

```lean
abbrev cohomology (R) [CommRing R] (X : TopCat.{0}) (n : ℕ) : ModuleCat R
def cup {X} {p q} : cohomology R X p → cohomology R X q → cohomology R X (p + q)
def one (R) [CommRing R] (X) : cohomology R X 0
theorem cup_assoc, cup_one, one_cup, cup_add_left/right, cup_smul_left/right,
        cohPullback_cup, cross, cross_natural
```

The join is the **even** subring

```text
A := ⨁_{n : ℕ} H^{2n}(X; ℤ),
```

which is a genuine `CommRing` — graded commutativity is honest commutativity in
even total degree — and is exactly the `A` every statement in this file is stated
over, since Chern classes live in even degrees only.

Everything needed for that direct sum to be a `CommRing` is present **except one
theorem**: graded commutativity

```lean
theorem cup_comm {X} {p q} (a : cohomology R X p) (b : cohomology R X q) :
    cup a b = (-1 : R) ^ (p * q) • cohCast R X (Nat.add_comm q p) (cup b a)
```

`cup_assoc`, `cup_one`, `one_cup` and bilinearity are already there.  So the
single blocking item between the cohomology lane and the whole Chern layer is
`cup_comm`, plus the `DirectSum` packaging.  That is worth saying plainly,
because it is one theorem and not a programme.

## 4. Withdrawn

`ChernParityCoefficient.lean` and `ChernNewtonSquareZero.lean` duplicated the
multinomial parity (2.8) and the square-zero step (2.7) already carried by the
parity lane; deleted rather than left as a second proof of the same thing.
