# Lane `cc-wu`

Owns `GroupApproximation/CharClass/Wu*.lean` and
`GroupApproximation/CharClass/ParityEven*.lean`, namespace
`GroupApproximation.CharClass`.  Deliverables: the `MvPolynomial` half-antidiagonal
identity, (Wu-diag) for mod-2 Chern classes, and Step D (the even side of Lemma 2).

## 0. Modules

| module | contents |
|---|---|
| `CharClass/WuSymmetric.lean` | `esymmOn`, `esymmHalf`, `esymmWuRHS`, the half-antidiagonal identity, the odd-antidiagonal vanishing, the pair reindexing, and the `MvPolynomial (Fin n) (ZMod 2)` corollaries |
| `CharClass/WuDiagonal.lean` | `SqData`, `wuMonomialOn`, `Sq` of a squarefree monomial, **(Wu-diag)** |
| `CharClass/ParityEvenSlice.lean` | `sliceClass = ∏_j (1 + h_j)^{d_j}`; its zero coefficient, its Frobenius evenness for `d_j` even, its vanishing above `∑ d_j` |
| `CharClass/ParityEven.lean` | `ParityData`, the convolution identity, `b_odd_eq_zero`, `gamma_top_eq_zero` |
| `CharClass/ParityInstance.lean` | `ParityData` assembled at `TotalH Y` / `TotalH N` over named hypotheses (namespace `GroupApproximation.CharClass.Wu`) |
| `CharClass/SqDataInstance.lean` | `SplittingData`, the `SqData` of the flag bundle, (Wu-diag) pushed down to `N`, and the endpoint with `hwu` and the per-space Cartan removed |
| `CharClass/ParityEvenTransport.lean` | functoriality of `TotalH.map`, the one model homeomorphism `lixN dd ≅ KnTwo.NTop (baseY dd)`, and the even side carried to the geometric model |

## 1. GREEN

All four modules, one probe, 2026-09-05:

```text
lake build GroupApproximation.CharClass.WuSymmetric GroupApproximation.CharClass.WuDiagonal \
           GroupApproximation.CharClass.ParityEvenSlice GroupApproximation.CharClass.ParityEven
ERROR_LINES=0
Build completed successfully (1553 jobs).
```

Freshly elaborated, not replayed: the four `.olean` files in the `cc-wu` clone
carry the timestamps of that run (`WuSymmetric` 18:44:07, `WuDiagonal` 18:44:15,
`ParityEvenSlice` 18:47:21, `ParityEven` 18:50:17).  No `sorry`, `admit`,
`axiom`, `opaque` or `native_decide` anywhere in the lane.

`CharClass/ParityInstance.lean`, one probe, 2026-09-05:

```text
lake build GroupApproximation.CharClass.ParityInstance
ERROR_LINES=0
Build completed successfully (8783 jobs).
```

Freshly elaborated: `ParityInstance.olean` written at 20:13:35 by that run.

`CharClass/SqDataInstance.lean`, 2026-09-05:

```text
lake build GroupApproximation.CharClass.SqDataInstance
ERROR_LINES=0
Build completed successfully (8786 jobs).
```

Freshly elaborated: `SqDataInstance.olean` written at 20:27:35 by that run.
Re-probed jointly with `cc-lix-odd`'s consumer module after adding `HasSplitting`:

```text
lake build GroupApproximation.CharClass.SqDataInstance GroupApproximation.CharClass.LemmaTwoStepD
ERROR_LINES=0
Build completed successfully (8807 jobs).
```

Deliverables 1, 2 and 3 of the lane brief are therefore complete and verified,
and the integration assembly is green over its named hypotheses.

## 2. AUTHORED, UNVERIFIED

Nothing.

## 3. NEEDS

Nothing from a peer for deliverables 1–3: the whole lane is Mathlib-only plus its
own files.  The consumers of this lane need to supply the `ParityData` fields in
§4 and the `SqData` fields in §5.

## 4. `ParityData`, the exact fields (for `cc-lix-odd` and the lead)

`GroupApproximation.CharClass.ParityData R H` with `[CommRing R] [CommRing H]`.
`R` is `H^*(Y; F₂)` for `Y = ∏_j CP(d_j)`, `H` is `H^*(N; F₂)` for
`N = S¹ × S⁵ × Y`, both as **single ungraded rings** (the grading enters only
through the `sq_b` field, see the note after the table).

```lean
structure ParityData (R H : Type*) [CommRing R] [CommRing H] where
  two_eq_zero  : (2 : R) = 0
  ι            : R →+* H
  t            : H
  x            : H
  t_mul_t      : t * t = 0
  tx_inj       : ∀ u v : R, ι u + t * x * ι v = 0 → v = 0
  SqH          : ℕ → H →+ H
  SqR          : ℕ → R →+ R
  sqH_zero_apply : ∀ c : H, SqH 0 c = c
  cartanH      : ∀ (n : ℕ) (u v : H),
                   SqH n (u * v) = ∑ p ∈ Finset.range (n + 1), SqH p u * SqH (n - p) v
  sqH_t        : ∀ n : ℕ, 0 < n → SqH n t = 0
  sqH_x        : ∀ n : ℕ, 0 < n → SqH n x = 0
  sqH_ι        : ∀ (n : ℕ) (r : R), SqH n (ι r) = ι (SqR n r)
  γ            : ℕ → H
  a            : ℕ → R
  b            : ℕ → R
  γ_eq         : ∀ k : ℕ, γ k = ι (a k) + t * x * ι (b k)
  a_zero       : a 0 = 1
  a_odd        : ∀ q : ℕ, Odd q → a q = 0
  sq_b         : ∀ k j : ℕ, 2 * k < j + 6 → SqR j (b k) = 0
  wu           : ∀ i : ℕ, SqH (2 * i) (γ (i + 1))
                   = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)
```

What each field is, concretely:

* `ι` — the Künneth inclusion `H^*(Y) → H^*(N)`, i.e. pullback along the
  projection `N → Y`.  A ring map, so `map_mul`/`map_add`/`map_sum` are free.
* `t`, `x` — the degree-1 generator of `H^*(S¹)` and the degree-5 generator of
  `H^*(S⁵)`, pulled back to `N`.  Note `z := t * x` has degree 6, so
  `γ_k = ι(a k) + z ι(b k)` puts `a k` in degree `2k` and `b k` in degree
  `2k − 6`; **`b k` is indexed by the total index `k`, not by its own degree.**
  In particular `b 0 = b 1 = b 2 = 0`, which is forced by `γ_eq` at `k < 3`
  together with the decomposition, and is *not* a separate field.
* `t_mul_t` — `t ⌣ t ∈ H²(S¹) = 0`.  Only `t² = 0` is needed; `x² = 0` is not
  used anywhere, so it is not a field.
* `tx_inj` — the only Künneth input: the `t x`-coordinate of
  `ι u + t x ι v` determines `v`.  Weaker than a full four-fold splitting, and
  it is what a Künneth isomorphism gives immediately.
* `sqH_t`, `sqH_x` — naturality plus vanishing of `H^{>1}(S¹)`, `H^{>5}(S⁵)`.
  Together with `cartanH` and `sqH_zero_apply` they give
  `SqH n (t x ι r) = t x ι (SqR n r)` (`ParityData.sqH_tx_mul`, proved here).
* `sq_b` — **the only place a grading on `R` is used.**  The statement is
  instability, `Sq^j = 0` above the degree, applied to `b k` of degree `2k − 6`:
  `2k − 6 < j` is written `2 * k < j + 6` to keep natural subtraction out of it.
  For `k ≤ 2` the hypothesis is vacuously satisfiable because `b k = 0` there.
  An instantiator with a graded `R` proves this in one line.
* `a_zero`, `a_odd` — supplied by `ParityEvenSlice.lean` when
  `a q = (sliceClass u h d).coeff q` with every `d j` even:
  `sliceClass_coeff_zero` and `sliceClass_coeff_odd_eq_zero`.
* `wu` — (Wu-diag), supplied by `WuDiagonal.SqData.wu_diagonal` after the
  splitting principle transports it from the flag bundle.

Conclusions available:

```lean
theorem ParityData.sum_a_mul_b_eq_zero (P : ParityData R H) (i : ℕ) :
    ∑ q ∈ Finset.range (2 * i + 1 + 1), P.a q * P.b (2 * i + 1 - q) = 0
theorem ParityData.b_odd_eq_zero (P : ParityData R H) : ∀ N : ℕ, Odd N → P.b N = 0
theorem ParityData.gamma_top_eq_zero (P : ParityData R H) {m : ℕ}
    (hm : Even m) (ha : ∀ q : ℕ, m < q → P.a q = 0) : P.γ (m + 3) = 0
theorem ParityData.gamma_top_eq_zero_of_slice (P : ParityData R H) {J : Type*}
    (u : Finset J) (h : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, P.a q = (sliceClass u h d).coeff q) :
    P.γ ((∑ j ∈ u, d j) + 3) = 0
```

The last one is the intended entry point: it needs only that the slice class of
`W` is `∏_j (1 + h_j)^{d_j}` with each `d_j` even, and returns `γ_r(W) = 0` for
`r = (∑_j d_j) + 3`.  **The statement is rank-free**: the rank of `W` is never
mentioned.

## 5. `SqData`, the exact fields (for `cc-projective`, `cc-steenrod`, `cc-cartan`)

`GroupApproximation.CharClass.SqData σ A` with `[CommRing A]`; `A` is the mod-2
cohomology ring of the flag bundle and `y` is the family of Chern roots.

```lean
structure SqData (σ : Type*) (A : Type*) [CommRing A] where
  two_eq_zero   : (2 : A) = 0
  Sq            : ℕ → A →+ A
  sq_zero_apply : ∀ a : A, Sq 0 a = a
  cartan        : ∀ (n : ℕ) (u v : A),
                    Sq n (u * v) = ∑ p ∈ Finset.range (n + 1), Sq p u * Sq (n - p) v
  s             : Finset σ
  y             : σ → A
  sq_y_one      : ∀ k : σ, Sq 1 (y k) = 0
  sq_y_two      : ∀ k : σ, Sq 2 (y k) = y k ^ 2
  sq_y_high     : ∀ (k : σ) (n : ℕ), 3 ≤ n → Sq n (y k) = 0
```

with `SqData.gamma D j := esymmOn D.s D.y j` and

```lean
theorem SqData.wu_diagonal (D : SqData σ A) [DecidableEq σ] (i : ℕ) :
    D.Sq (2 * i) (D.gamma (i + 1))
      = ∑ j ∈ Finset.range (i + 1), D.gamma (i - j) * D.gamma (i + 1 + j)
```

`sq_y_one`/`sq_y_two`/`sq_y_high` are exactly "`y k` has degree 2 and
`Sq(y k) = y k + y k ^ 2`" with the grading forgotten; no instability field and
no `Sq n 1 = 0` field is needed — the latter is **derived** from `cartan` and
`sq_zero_apply` (`SqData.sq_one_eq_zero`).

## 6. Mathematics: where this departs from the design source

1. **`d_j` even suffices; the power-of-two hypothesis is not needed.**
   `research/artifacts/stw59-obstruction-lean-routes-2026-09-05.md` §9.6 insists
   that "`d_j` a power of two is load-bearing, not cosmetic", because its
   induction on `|J|` restricts to sub-products and needs each `a_q` to be a
   single squarefree monomial `μ_S`.  That is an artefact of *that* induction.
   The route taken here never restricts to a sub-product.  Reading the
   `t x`-component of (Wu-diag) at every `i` and reindexing both halves by the
   total index turns the whole family of relations into the single statement

   > `(a ⋆ b)_N = 0` for every odd `N`,   `⋆` = convolution of sequences,

   after which `a_0 = 1` and `a_q = 0` for odd `q` give `b_N = 0` for every odd
   `N` by strong induction on `N` (the terms with `q ≥ 2` even have `N − q` odd
   and smaller).  Only "`a` is supported in even indices and `a_0 = 1`" is used,
   and that is exactly Frobenius evenness, which holds for every even `d_j`
   (`(1+h)^d = ((1+h)^{d/2})²`).  Checked by hand at `d = 6`, where §9's
   sparsity fails and this argument still closes.
   This matches `notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3, which already
   states Lemma 2 for `d j` merely even and positive.  (Positivity is not used
   either.)

2. **Index convention.**  The route document writes `γ(W) = a + t x b` and calls
   the top component `b_m` with `m = ∑ d_j`, indexing `b` by *its own* degree
   halved.  The Lean here indexes `b` by the **total** index: `γ_k = ι(a_k) + z
   ι(b_k)` with `deg(b_k) = 2k − 6`.  The two differ by 3, and the target is
   `b_r` with `r = m + 3`, which is odd exactly because `m` is even.  With the
   document's convention the relation is not a convolution and the bookkeeping
   of §9.3 has to carry the shift by hand; with the total index it is.

3. **The Wu instance to use.**  The document's §9.3 instantiates at
   `n = m`, `i = m/2 + 1`.  The program note's §1.3 phrases the same instance as
   `(j, k) = (n/2 − 1, n/2 + 1)`, i.e. "kill `b_n` for even `n`".  Both are the
   `i = m/2 + 1` instance of (Wu-diag).  In the total-index convention no
   instance has to be selected at all: *every* `i` is used, and the family of
   relations is equivalent to the convolution statement.

4. **The `MvPolynomial` identity is proved by induction on the index set, not by
   the generating function.**  §10.3 proposes `∏_k (1 + 2 y_k T + y_k² T²)` over
   `ℤ`, halving the coefficient of `T^{2i+1}`.  In Lean that costs a coefficient
   extraction from a `Finset` product of three-term factors plus a division in
   `ℤ[y]`.  Both sides of the identity satisfy the *same* recursion under
   `s ↦ insert w s`,

   ```text
   F (insert w s) (c+1) = F s (c+1) + y_w · (e_{c+1}(s))² + y_w² · F s c,
   ```

   agree at `i = 0` (both are `e_1`) and at `s = ∅` (both are `0`); that is the
   whole proof, entirely inside characteristic two.  The `2^{|U|−1}` step of
   §10.3 disappears.  The full antidiagonal `∑_{a+b=2i+1} e_a e_b = 0` is a
   separate three-line pairing argument (`sum_antidiagonal_self_eq_zero`).

5. **The derivative identity.**  A third proof of the same identity is
   `E · ∂_T E = ∑_k y_k (1 + y_k T) ∏_{l ≠ k} (1 + y_l² T²)`, whose `T^{2i}`
   coefficient is the right-hand side while the left-hand side is the half
   antidiagonal (mod 2, `b · e_b` selects one member of each pair `{a, b}` with
   `a + b = 2i + 1`).  Recorded because it is short on paper; not formalized,
   because matching "one member of each pair" to "`a ≤ i`" needs a bijection
   through unordered pairs, which is more Lean work than the induction.

## 7. `ParityInstance.lean`: the checklist for the topology lanes

`CharClass/ParityInstance.lean` (namespace `GroupApproximation.CharClass.Wu`)
instantiates `ParityData` at `R := TotalH Y`, `H := TotalH N` — the mod-2
cohomology rings of `ChernTotalRing.lean` — through

```lean
def parityData_of
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan …) (htx_inj …) (hγ …) (ha_zero …) (ha_odd …) (hsq_b …) (hwu …) :
    ParityData (TotalH Y) (TotalH N)
```

with `t := tClass q₁ σ₁ = TotalH.map q₁ (TotalH.of S₁ 1 σ₁)` and
`x := xClass q₅ σ₅ = TotalH.map q₅ (TotalH.of S₅ 5 σ₅)`.

**Discharged today** (no hypothesis): `two_eq_zero` (`totalH_two_eq_zero`),
`ι = TotalH.map p`, `t`, `x`, `t_mul_t` (`mul_self_pull_sphere_eq_zero`),
`SqH = Steenrod.SqH N`, `SqR = Steenrod.SqH Y`, `sqH_zero_apply`
(`Steenrod.SqH_zero_apply`), `sqH_t` and `sqH_x`
(`sq_pull_sphere_eq_zero`: naturality plus the sphere's vanishing — neither
needs instability nor Cartan), `sqH_ι` (`Steenrod.SqH_map`, on the nose).

**The remaining hypotheses**, name, statement, owner.  Seven for
`parityData_of`, but `ha_zero` and `ha_odd` are consequences of the slice
hypothesis, so the endpoint `gamma_top_eq_zero_of_slice_totalH` asks for only
**five**:

| name | statement | owner |
|---|---|---|
| `hcartan` | `∀ (n : ℕ) (u v : TotalH N), Steenrod.SqH N n (u * v) = ∑ i ∈ Finset.range (n+1), Steenrod.SqH N i u * Steenrod.SqH N (n-i) v` | `cc-cartan` (formula), `cc-steenrod` (transport to `SqH` on `TotalH`) |
| `htx_inj` | `∀ u v : TotalH Y, TotalH.map p u + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0` | **CLOSED**: `cc-cohom-api`'s `KnTwo.htx_inj` (8816 jobs), at the concrete model `(Y × S⁵) × S¹` |
| `hγ` | `∀ k : ℕ, γ k = TotalH.map p (a k) + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p (b k)` | **CLOSED over `ChernSplit`**: `cc-cohom-api`'s `KnTwo.hgamma_and_hsq_b` (8821 jobs) |
| `ha_zero` | `a 0 = 1` | `cc-projective` (slice restriction); free from `hslice` below |
| `ha_odd` | `∀ q : ℕ, Odd q → a q = 0` | `cc-projective`; free from `hslice` below |
| `hsq_b` | `∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0` | **CLOSED over `ChernSplit`**: same theorem, through this lane's `sq_b_of_grading` |
| `hwu` | `∀ i : ℕ, Steenrod.SqH N (2*i) (γ (i+1)) = ∑ j ∈ Finset.range (i+1), γ (i-j) * γ (i+1+j)` | `cc-projective` (splitting principle) + `cc-steenrod`/`cc-cartan`, through `SqData.wu_diagonal` |

Helpers that make three of these mechanical:

* `sq_b_of_grading (b) (hlow : ∀ k < 3, b k = 0) (hdeg : ∀ k c, 2*k = c+6 → ∃ β : Hmod2 Y c, b k = TotalH.of Y c β) : hsq_b`.
  Note the `k < 3` clause: `t x` already carries degree six, so `b 0 = b 1 = b 2`
  are forced to vanish and the `sq_b` field asserts exactly that at `j = 0`.
* `a_zero_of_slice` and `a_odd_of_slice` derive `ha_zero` and `ha_odd` from
  `hslice : ∀ q, a q = (sliceClass u h d).coeff q` together with
  `hd : ∀ j ∈ u, Even (d j)`, via `sliceClass_coeff_zero` and
  `sliceClass_coeff_odd_eq_zero`.

The endpoint delivered to `cc-lix-odd` is

```lean
theorem gamma_top_eq_zero_of_slice_totalH … : γ ((∑ j ∈ u, d j) + 3) = 0
```

taking only `hcartan`, `htx_inj`, `hγ`, `hsq_b`, `hwu` plus `(u, h, d)`,
`hd` and `hslice`.  It is rank-free: the rank of `W` is never mentioned.

## 8. `SqDataInstance.lean`: `hwu` and the per-space Cartan removed

`hwu` is no longer an input.  `CharClass/SqDataInstance.lean` builds the `SqData`
of the flag total space, proves (Wu-diag) there by `SqData.wu_diagonal`, and
pushes it down to `N` along the injective pullback.  What replaces it is one
bundled input from `cc-projective`:

```lean
structure SplittingData (N F : TopCat.{0}) (r : ℕ) (γ : ℕ → TotalH N) where
  proj : F ⟶ N
  root : ℕ → Hmod2 F 2
  pull_injective : Function.Injective (TotalH.map proj)
  sq_one_root : ∀ l : ℕ, Sq 1 (root l) = 0
  chern_split : ∀ k : ℕ,
    TotalH.map proj (γ k) = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k
```

`sq_one_root` is the only Steenrod-flavoured field: `H³(ℂP^{K-1}; F₂) = 0` plus
naturality.  `Sq^0 = id`, `Sq² root = root²` and `Sq^j root = 0` for `j ≥ 3` are
proved here from `SteenrodTotal`, because `TotalH.of F 2 β` carries its degree.

Two further collapses:

* `CartanTotal := ∀ X, Steenrod.CartanOf X` is `cc-cartan`'s formula quantified
  over the space; `cartanH_of` turns it into the `cartanH`/`cartan` field at any
  space through `cc-steenrod`'s `Steenrod.SqH_mul_of_cartanOf`.  So the whole
  chain has **one** Cartan hypothesis, not one per space.
* `tx_inj_of_degreewise` converts a **degreewise** two-sphere Künneth statement
  into the ring-level `tx_inj` field.  **Now redundant**: `cc-cohom-api` proved
  `KnTwo.htx_inj` directly at the concrete model `(Y × S⁵) × S¹`
  (`CharClass/CohomologyParityKunneth.lean`, 8816 jobs), which is simpler, and
  they are right that the field cannot hold for abstract projections.  The lemma
  is left in place as an unused alternative route; do not build on it.  What did
  carry over from this lane is `totalH_component_map`, which they use, and the
  unreduced-index convention.
* `totalH_map_injective` converts `cc-projective`'s degreewise Leray–Hirsch
  injectivity (`∀ n, Function.Injective (pull f n)`) into the ring-level
  `Function.Injective (TotalH.map f)` that `SplittingData` asks for.  Degreewise
  is the form they actually have, so without this the field could not be
  discharged.

For a consumer whose record does not otherwise mention the flag bundle,
`HasSplitting N γ` is the same input with `F` and `r` existentially quantified,
so it is one `Prop`-valued field rather than two type parameters plus a field;
`gamma_top_eq_zero_of_hasSplitting` is the matching endpoint.

The endpoint is then `gamma_top_eq_zero_of_splitting`, with **four** hypotheses:
`hC : CartanTotal` (cc-cartan), `htx_inj` and `hγ` and `hsq_b` (cc-cohom-api),
plus `S : SplittingData` (cc-projective) and the slice data `(u, h, d, hd,
hslice)` (cc-projective).

## 8b. Where the even side actually stands

Three of the four hypotheses of `gamma_top_eq_zero_of_splitting` are now closed
or reduced to one input:

* `htx_inj` — closed outright.
* `hγ` and `hsq_b` — closed.  `cc-cohom-api`'s `KnTwo.chernSplit_of_noOdd`
  (8822 jobs) builds `ChernSplit` from exactly two inputs: `γ k` concentrated in
  degree `2k`, which `cc-projective`'s `LerayHirschGraded.gamma` gives by its
  type, and `KnHemi.NoOddCohomology Y`.  No fact about Chern classes enters.  The
  `split` field is no longer a hypothesis anyone proves by hand.
* `KnHemi.NoOddCohomology Y` — the one genuinely open statement in this part of
  the chain.  It appears only as a hypothesis (`decomp_even`, `decomp_even_low`,
  `chernSplit_of_noOdd`) and is proved nowhere for a product of projective
  spaces.  Owner `cc-projective`, reassigned from `cc-thom` (whose vanishing-form
  toolkit cannot express it).
* `hC : CartanTotal` — `cc-cartan`, unchanged.
* `hsplit : HasSplitting` and `hslice` — `cc-projective`, both behind
  Leray–Hirsch.

**Range remark for whoever writes `chernSplit_of_hodd`.**  The degree-five
coordinate exists only for total degree `≥ 5` and the degree-one coordinate only
for `≥ 1`.  Below those the term is *absent*, not sitting in a truncated ℕ
degree — `m - 5` at `m = 4` is `0`, which is even, and the odd-degree argument
would look wrong there.  That is the one place the corollary can go astray.

## 8c. The model seam, and the transport

The even and odd sides were each green over a **different** model of `N`:
`cc-cohom-api`'s Künneth work at `KnTwo.NTop Y = (Y × Sphere 5) × Sphere 1` with
the vendored spheres, and `cc-thom`/`cc-lix-odd` at
`lixN dd = ↥sphereOne × baseM dd`, that is `S¹ × (S⁵ × Y)`, with the Hermitian
unit sphere of `ℂ³`.  Both correct, about different spaces.  By the lead's
ruling the geometric model wins and `CharClass/ParityEvenTransport.lean` carries
the even side across (green, 8896 jobs).

What made it one homeomorphism rather than four transports: pullback along an
isomorphism is injective on `TotalH` (`totalH_map_injective_of_iso`), which
follows from functoriality alone, so each statement crosses by applying
`TotalH.map` and cancelling.  `totalH_map_comp` and `totalH_map_id` did not
exist and are proved here.  **`hsq_b` needs no transport at all**: neither `N`
nor the model occurs in it.

Three points settled by peers rather than guessed, all confirmed by the probe:

* `↥sphereOne` and the vendored `Sphere 1` are the same subtype, so the circle
  bridge is `Homeomorph.refl`.  Evidence `cc-lix-odd` gave: `hasTopLine_sphereOne`
  is the vendored lemma applied with nothing between.
* No `prodAssoc` is needed — `baseM` already carries the pair on the inside, so
  two commutations and a congruence do it.
* The two `baseY` in the repo (`CharClass.baseY` on a dimension vector,
  `STW59.baseY` on a stage number) do **not** collide in practice: they take
  different argument types and elaboration disambiguates.

## 9. TRAPS

* **`autoImplicit` silently swallowed a missing `import`.**  `ZMod` was unknown
  in `WuSymmetric.lean` and `autoImplicit` turned it into an implicitly bound
  variable, so the error surfaced as `Function expected at ZMod`, followed by two
  `isDefEq`/`whnf` heartbeat timeouts and a cascade of `Unknown identifier`s for
  declarations later in the same file.  Fix: `import Mathlib.Data.ZMod.Basic`,
  and `set_option autoImplicit false` at the top of every file in this lane so
  the next such slip is a one-line error instead of a cascade.
* **Read the whole probe log, not its tail.**  The first probe was piped through
  `tail -80`, which cut off the error list the helper prints *before* the log
  tail; the visible part was entirely cascade damage.  Use `CC_TAIL` and capture
  the full output.
* **`Nat.succ` versus `n + 1` after `cases`.**  Several rewrites here need the
  index in the literal form `n + 2` (for `sqShift`) or `2 * c' + 2` (for the
  induction hypotheses).  Every branch of a `cases`/`rcases` on `ℕ` opens with a
  `show` in the intended literal form; `show` checks up to definitional
  equality, so `2 * (c' + 1)` and `2 * c' + 2` are interchangeable there but not
  under `rw`.
* **A tactic-mode `match` on a variable that a hypothesis mentions is wrong.**
  `match p with | 0 => …` substitutes in the goal but not in `hp : ¬p = 0 ∧ …`,
  so the branch cannot use `hp`.  Nested `rcases p with _ | p` does substitute.
  (`interval_cases` would too, but `Mathlib.Tactic.IntervalCases` is not in the
  transitive import closure of this lane's files.)
* **`Finset.sum_image` takes `Set.InjOn`, not the pairwise form** at this pin,
  and `Finset.powersetCard_succ_insert` is stated with `n.succ`, so its instance
  has to be produced as a `have` with `a + 1` written out before it can be
  `rw`-ed into a goal that shows `a + 1`.
* **`Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` lands on `range n.succ`**,
  which is only definitionally `range (n + 1)`; finish with `exact`, not `rw`.
* Deprecated `not_mem` spellings: at this pin the names are
  `Finset.card_insert_of_notMem`, `Finset.insert_sdiff_of_notMem`.
* **A degree written as a sum never matches a lemma stated at a literal.**
  The general form of the hazard below, found independently by `cc-projective`:
  `Sq^1` of a degree-two class has degree `1 + 2`, and handing that to a lemma
  stated at the literal `3` sends the elaborator into a deterministic `isDefEq`
  timeout at 200000 heartbeats.  Their fix is the right general one and is better
  than "leave indices unreduced": **state the vanishing at an arbitrary degree
  with the side condition as a hypothesis**, so no literal is ever matched
  against a sum.
* **Never add two degrees inside a `TotalH.of`.**  Writing the product of the
  degree-1 and degree-5 generators as one class in degree `6` asks Lean for
  `Hmod2 N (1 + 5) = Hmod2 N 6`; it unfolds the cohomology construction instead
  of reducing the index first and dies on a deterministic `isDefEq` timeout at
  200000 heartbeats, taking the rest of the file with it.  Peel one generator at
  a time and leave the index unreduced as `1 + (5 + n)`.  The same hazard applies
  at any boundary between lanes: a statement handed over at `6 + n` forces the
  identical defeq on whoever converts it.  `cc-cohom-api` adopted the convention
  and their `KnTwo.tClass_mul_xClass` is stated at `TotalH.of _ (1 + 5)`.
* **Name ambiguity, RESOLVED.**  There were briefly two `component_of_mul`, one
  at the bare `CharClass` level and this lane's in `CharClass.Wu`.  A file
  `open`ing both would have got a real ambiguity error.  `cc-cohom-api` moved
  theirs into `CharClass.KnTwo`, which is where the fleet convention puts it
  anyway, so nothing of this lane changed.  Two declarations sharing a short name
  at different namespace depths is silent until someone opens both — worth a look
  whenever a lane lands a helper at the bare level.
