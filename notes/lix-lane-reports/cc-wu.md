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
| `CharClass/ParityEvenFlag.lean` | pullback injectivity along the flag tower, composed from the per-stage projections |
| `CharClass/ParityEvenFlagCompact.lean` | compactness and non-emptiness of every stage, and the flag pullback injective unconditionally |
| `CharClass/ParityEvenSplitting.lean` | `Wu.HasSplitting` for a compact rooted base, over the split relation at the flag |
| `CharClass/ParityEvenFlagRelation.lean` | the split relation at the flag, and so **the splitting principle with nothing left open** |
| `CharClass/ParityEvenLixSplitting.lean` | concentration of a Chern class with a splitting, and `hsplit` for the LIX mapping torus |
| `CharClass/ParityEvenStepDClosed.lean` | Step D's data over the slice value alone, and Lemma 2 over two inputs |
| `CharClass/ParityEvenVSlice.lean` | `VSliceValue`, the last input stated about `V` alone, and the bridge to the assembly |

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

`CharClass/ParityEvenTransport.lean`, 2026-09-05:

```text
lake build GroupApproximation.CharClass.ParityEvenTransport
ERROR_LINES=0
Build completed successfully (8896 jobs).
```

Freshly elaborated: olean written 22:46:04.  Landed as `6efca320d`, verified by
`git merge-base --is-ancestor` against `origin/main`, not by the push message.

`CharClass/ParityEvenFlag.lean`, 2026-09-05: 9039 jobs, landed `aba9f26c3`.

`CharClass/ParityEvenFlagCompact.lean`, 2026-09-05: 9140 jobs, landed `c8f2bbec2`.

`CharClass/ParityEvenSplitting.lean`, 2026-09-06:

```text
lake build GroupApproximation.CharClass.ParityEvenSplitting
ERROR_LINES=0
Build completed successfully (9170 jobs).
```

Landed `2bb3ca080`.

`CharClass/ParityEvenFlagRelation.lean`, 2026-09-06:

```text
lake build GroupApproximation.CharClass.ParityEvenFlagRelation
ERROR_LINES=0
Build completed successfully (9172 jobs).
```

Landed `aed680f94`.  With it `Wu.hasSplitting_flag` is unconditional: over a
compact non-empty base a bundle of constant positive rank has a `SplittingData`,
with no hypothesis of any kind beyond that.

`CharClass/ParityEvenLixSplitting.lean`, 2026-09-06:

```text
lake build GroupApproximation.CharClass.ParityEvenLixSplitting
ERROR_LINES=0
Build completed successfully (9177 jobs).
```

`Wu.hasSplitting_lix G hGc hGu : Wu.HasSplitting (lixN dd) (lixChernOf (lixChern
dd) (mappingTorus Vmat G circHoriz circHeight))`, which is `WuStepDPinned.hsplit`
verbatim.  The round trip `TotalH.of ∘ TotalH.component` between the ring-level
`chern` and `lixChernOf`'s degreewise form is absorbed by `of_component_chern`,
which reads the concentration off the splitting's own `chern_split` field rather
than off any grading of the Chern classes.

`CharClass/ParityEvenStepDClosed.lean`, 2026-09-06:

```text
lake build GroupApproximation.CharClass.ParityEvenStepDClosed
ERROR_LINES=0
Build completed successfully (9197 jobs).
```

`lemmaTwoHolds_of_exists_chernSliceValue : LIX.LemmaTwoHolds` over two inputs,
`cc-thom`'s Step C chain and `LixSliceValue`, the value of the Chern classes on
the south slice.  The generators are existentially quantified rather than named by
the consumer, so nobody can supply generators the value statement was not proved
for.  Both `#print axioms` report `[propext, Classical.choice, Quot.sound]`.

Re-probed at 9198 jobs after citing `cc-lix-odd`'s
`unitVectorsThreeHomeoSphere_symm_apply_negEThree` for the point equality, landed
`bf99deceb`.  Their map-level `lixSliceMap_south_marked` does **not** apply here:
`chernOf` takes the restricted rank as a proof argument whose type mentions the
slice map, so moving the map is a dependent rewrite whose motive does not
typecheck, while substituting the point moves the map and the rank proof together.

### What the even side now rests on

`lemmaTwoHolds_of_vSliceValue` needs two things and nothing else: `cc-thom`'s
Step C chain, and `VSliceValue`, the statement that the mod-2 Chern classes of `V`
over the projective base are the coefficients of `∏_j (1 + gen_j)^{d_j}` for some
generators.  The second is `cc-steenrod`'s, who have confirmed it is the statement
they will prove.

`CharClass/ParityEvenVSlice.lean`, 2026-09-06:

```text
lake build GroupApproximation.CharClass.ParityEvenVSlice
ERROR_LINES=0
Build completed successfully (9199 jobs).
```

### The rule-17 comparison (assigned by the lead, done before `cc-steenrod` landed)

`VSliceValue` against `LixSliceValue`, binder by binder: the generators agree, both
being a parameter the bridge passes through untouched; the base space agrees; the
coefficient convention agrees, both sides being `KnTwo.ChernSliceValue` whose
right-hand side is the slice polynomial's *coefficient*, so reciprocal Vieta never
crosses the interface; the rank arguments differ in spelling and cannot matter,
being proofs.  The one real gap is the index type and the bundle,
`VIdx dd ⊕ VIdx dd` against `VIdx dd`, closed by `cc-steenrod`'s own
`LH.chernOf_lixSlice_eq_vBundleY` in a single `congrArg`.

Because `VSliceValue` mentions no mapping torus, the existential over generators is
per **stage** rather than per mapping torus, a smaller input than the one it
replaces.

Re-probed at 9208 jobs after adding `lemmaTwoHolds_of_sliceGen`, landed
`1e76e9be9`.  That endpoint takes the value statement at `cc-projective`'s
`LH.sliceGen` and introduces the existential itself, so `cc-steenrod`'s theorem
lands with no introduction step in between.  Positivity at every stage is
`LIX.lixDD_pos`, a theorem, so it is not a hypothesis.  The family is forced rather
than chosen: `sliceGen_eq_root` says every line of `V` over factor `j` carries that
class, so `sliceClass`'s multiplicity is a fact and not a convention.  Both the
existential and the pinned form stand; the pinned one is the one to cite.

Deliverables 1, 2, 3 and 4 of the lane brief are complete and verified, the
integration assembly is green over its named hypotheses, and the even side is
stated at the model of record.  `cc-lix-odd` consumes it in
`CharClass/LemmaTwoStepDLix.lean` (8900 jobs), where Step C and Step D are now
statements about **one class on one space**.

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

## 10. Content-duplicate sweep of `CharClass` (report only, assigned by the lead)

Over a clean `git archive` export of `origin/main` at `6aa6a2b79`, all 496 modules
of `GroupApproximation/CharClass`, 4341 declarations parsed, of which 3236 are
theorems or lemmas.  A declaration's statement was canonicalised by erasing
instance binders, erasing sort-valued binders (so that a binder in a `variable`
block and the same binder written inline compare equal), renaming every local by
order of first appearance in the conclusion, sorting the remaining hypothesis
types, and stripping namespace prefixes.  Two declarations are listed when the
canonical forms agree, whatever their names.

**21 cross-module content duplicates.**  Two further groups the scan returned are
not duplicates and are excluded: `CartanTargetSwap.pairModule_gen_smul` against
`pairModule_one_add_gen_smul`, where the conclusion begins with `letI` and the
source-level parser truncated it, and `BundleFrame.exists_isometry_aux` against
`exists_isometry_of_isStarProjection`, a private helper restated publicly in the
same module, which is deliberate.

"Imported by more" counts modules whose `import` line names the containing module.
"Used" counts modules elsewhere in the tree mentioning the declaration's final
name; for a same-named pair that count cannot distinguish the two and is shown for
both.

| # | A | B | owner lanes | imported by more | used A / B |
|---|---|---|---|---|---|
| 1 | `CohomologyBasic::cohCast_zero` | `CohomologyKunnethStep::cohCast_zero` | cc-cohom-api / cc-cohom-api | A (6 vs 2) | 18 / 18 |
| 2 | `SteenrodTargetLinear::dTgt_smul` | `CartanTargetFunctorial::dTgt_smul_tgtModule` | cc-steenrod / cc-cartan | tie (1 vs 1) | 4 / 1 |
| 3 | `ThomStepCOddIso::topChernClass_ne_zero_odd_iso` | `ThomStepCOddLocal::topChernClass_ne_zero_odd_local_of_iso` | cc-thom / cc-thom | A (3 vs 2) | 4 / 0 |
| 4 | `MayerVietorisPull::mvCxInclV_comp_g` | `CohomologyDeltaChain::mvCxInclV_comp_g` | cc-thom / cc-cohom-api | A (2 vs 1) | 2 / 2 |
| 5 | `SqDataInstance::component_of_mul` | `CohomologyParityKunneth::component_of_mul` | cc-wu / cc-cohom-api | A (5 vs 1) | 2 / 2 |
| 6 | `LerayHirschSquares::add_self` | `ParityInstance::hmod2_add_self` | cc-projective / cc-wu | tie (2 vs 2) | 2 / 0 |
| 7 | `SteenrodTotal::of_cohCast` | `ParityEvenLixSplitting::of_congr_degree` | cc-steenrod / cc-wu | A (4 vs 1) | 2 / 0 |
| 8 | `CartanComparison::pairFreeCx_d` | `SteenrodFourfoldBridge::pairFreeCx_d_eq` | cc-cartan / cc-steenrod | A (2 vs 1) | 1 / 0 |
| 9 | `SteenrodChainMapNat::pushSimplex_faceSimplex` | `CartanTargetFunctorial::pushSimplex_faceSimplex` | cc-steenrod / cc-cartan | A (3 vs 1) | 1 / 1 |
| 10 | `ChernLineEulerNatural::lineEulerOf_pushforward` | `SliceLineEulerPush::lineEulerOf_pushforward` | cc-projective / cc-steenrod | tie (0 vs 0) | 1 / 1 |
| 11 | `MayerVietorisPullAmbient::f_comp_mvCxProjU` | `CohomologyDeltaChain::f_comp_projU` | cc-thom / cc-cohom-api | A (3 vs 1) | 0 / 1 |
| 12 | `MayerVietorisPullAmbient::f_comp_mvCxProjV` | `CohomologyDeltaChain::f_comp_projV` | cc-thom / cc-cohom-api | A (3 vs 1) | 0 / 1 |
| 13 | `LerayHirschBridge::lhDomainCard_le` | `CohomologyLHRingPieces::lhDomainCard_le` | cc-projective / cc-cohom-api | A (3 vs 1) | 1 / 1 |
| 14 | `LIXChernSliceValueBridge::rank_vBundleY_lixRank` | `SliceSplitV::rank_vBundleY_lixRank` | cc-projective / cc-steenrod | A (1 vs 0) | 1 / 1 |
| 15 | `ParityEvenTransport::totalH_map_id` | `ThomChernBasis::totalMap_id` | cc-wu / cc-projective | A (3 vs 1) | 1 / 0 |
| 16 | `BundleInvariance::conjTranspose_absorb_left` | `BundleClassify::mul_conjTranspose_hom` | cc-bundle / cc-bundle | A (5 vs 2) | 0 / 0 |
| 17 | `BundleClassify::rot_coeff_pos` | `BundleStabilize::stabCoeff_pos` | cc-bundle / cc-projective | A (2 vs 1) | 0 / 0 |
| 18 | `CartanComposeA::awDiag_naturality` | `SteenrodFourfoldA::pairPushLin_awDiag` | cc-cartan / cc-steenrod | A (3 vs 1) | 0 / 0 |
| 19 | `CohomologyBasic::cohCast_congr` | `SteenrodCupOne::cohCast_congr_proof` | cc-cohom-api / cc-steenrod | tie (6 vs 6) | 0 / 0 |
| 20 | `CohomologyChartTowerTop::cupPowE_pull_eq_zero` | `LerayHirschRankVanish::cupPowE_pull_cpGen_eq_zero` | cc-cohom-api / cc-projective | tie (1 vs 1) | 0 / 0 |
| 21 | `ThomHabs::range_relToAbs_eq_ker_absToSub` | `RelativeRangeKer::relLES_range_eq_ker'` | cc-thom / cc-relative | A (1 vs 0) | 0 / 0 |

Five pairs cross a lane boundary in the direction the fleet has already been
bitten by: `component_of_mul`, `of_cohCast`/`of_congr_degree`, `totalH_map_id`,
`lhDomainCard_le` and `rank_vBundleY_lixRank` all restate a fact about a third
lane's object.  The `Cartan*` against `Steenrod*` family, rows 2, 8, 9 and 18, is
a single wave rather than four independent events: the two lanes built the same
fourfold-comparison layer under two prefixes.

Ownership above is read from the leading lane token of each module's commit
subjects.  `LIXChernSliceValueBridge` names no lane in its subject; it is
`cc-projective`'s, recorded from the board at `3f50a8dde`, batch 180.

Nothing was edited.  Retirement is the lead's to assign, after the endpoint and
under rule 11.

## 11. Repeated final names in `CharClass` (report only, assigned by the lead)

Same export, same parser.  A group is listed when two or more declarations have
different **full** names whose last component agrees.  **44 groups**, not the 40 I
first reported: that count came from a pass whose declaration regex excluded `.`,
so a dotted declaration such as `theorem Bundle.ext` was recorded under the name
`Bundle`.  The corrected pass is the one tabled here.

**No two declarations share a full name.**  That is the check worth stating: a
genuine duplicate declaration would red the root, and there is none.

"Co-open" says whether some module in `CharClass` has both namespaces in scope at
once, by `open` or by being inside one of them.  That is the condition under which
the short name is ambiguous and the failure is a type error far from the name,
which is the shape `cc-cohom-api` and `cc-steenrod` hit with `southPole`.  A group
with co-open "no" costs nothing today and only matters if some future module opens
both.

Many groups are structure projections — `.wu`, `.congr`, `.ext`, `.gamma`,
`.gamma_top_eq_zero` — where the structure namespace is doing exactly its job.
Those are marked so and are not retirement candidates.

| final name | used | kind | co-open | members (module :: full name) |
|---|---|---|---|---|
| `ext` *(structure projection)* | 64 | same | yes | `BundleBasic` :: `GroupApproximation.CharClass.Bundle.ext` (theorem, imp 4)<br>`CartanFourfold` :: `GroupApproximation.CharClass.FreeCxHom.ext` (theorem, imp 3)<br>`ProjectiveSpaceBasic` :: `GroupApproximation.CharClass.CPn.ext` (theorem, imp 1)<br>`SteenrodDiagonalTarget` :: `GroupApproximation.CharClass.Steenrod.PairDeg.ext` (theorem, imp 3) |
| `homotopy` *(structure projection)* | 56 | same | no | `AcyclicModels` :: `GroupApproximation.CharClass.NaturalHomotopy.homotopy` (def, imp 8)<br>`Cartan` :: `GroupApproximation.CharClass.DiagonalComparison.homotopy` (def, imp 1) |
| `wu` *(structure projection)* | 30 | same | no | `SqDataInstance` :: `GroupApproximation.CharClass.Wu.SplittingData.wu` (theorem, imp 5)<br>`SqDataInstance` :: `GroupApproximation.CharClass.Wu.HasSplitting.wu` (theorem, imp 5) |
| `congr` *(structure projection)* | 29 | same | no | `ThomPuncturedPi` :: `GroupApproximation.CharClass.PuncturedAcyclic.congr` (theorem, imp 2)<br>`ThomTopLine` :: `GroupApproximation.CharClass.HasTopLine.congr` (theorem, imp 1) |
| `puncturedSet` | 18 | **mixed** | yes | `BundleSpace` :: `GroupApproximation.CharClass.Bundle.puncturedSet` (def, imp 5)<br>`RelativeLocalModel` :: `GroupApproximation.CharClass.puncturedSet` (abbrev, imp 5) |
| `cohCast_zero` | 17 | same | yes | `CohomologyBasic` :: `GroupApproximation.CharClass.cohCast_zero` (theorem, imp 6)<br>`CohomologyKunnethStep` :: `GroupApproximation.CharClass.KnHemi.cohCast_zero` (theorem, imp 2) |
| `cpTaut` | 16 | same | yes | `BundleSpace` :: `GroupApproximation.CharClass.cpTaut` (def, imp 5)<br>`CohomologyChartRankTwoInterface` :: `GroupApproximation.CharClass.KnCP.cpTaut` (def, imp 2) |
| `gamma` *(structure projection)* | 16 | same | no | `LerayHirschDegree` :: `GroupApproximation.CharClass.LerayHirschGraded.gamma` (def, imp 2)<br>`WuDiagonal` :: `GroupApproximation.CharClass.SqData.gamma` (def, imp 1) |
| `WSIndex` | 13 | same | yes | `CartanDiagonalModule` :: `GroupApproximation.CharClass.WSIndex` (abbrev, imp 3)<br>`SteenrodDiagonalLambda` :: `GroupApproximation.CharClass.Steenrod.WSIndex` (abbrev, imp 1) |
| `compA` | 9 | same | yes | `CartanComposeA` :: `GroupApproximation.CharClass.compA` (def, imp 3)<br>`SteenrodFourfoldA` :: `GroupApproximation.CharClass.Steenrod.compA` (def, imp 1) |
| `pull_cohCast` | 9 | same | no | `CohomologyKunnethSurj` :: `GroupApproximation.CharClass.KnHemi.pull_cohCast` (theorem, imp 1)<br>`LerayHirschSquares` :: `GroupApproximation.CharClass.LH.pull_cohCast` (theorem, imp 2) |
| `chartSet` | 6 | same | yes | `BundleChart` :: `GroupApproximation.CharClass.Bundle.chartSet` (def, imp 1)<br>`ProjectiveSpaceChart` :: `GroupApproximation.CharClass.CPn.chartSet` (def, imp 4) |
| `awHom` | 3 | same | yes | `CartanComposeA` :: `GroupApproximation.CharClass.awHom` (def, imp 3)<br>`SteenrodFourfoldA` :: `GroupApproximation.CharClass.Steenrod.awHom` (def, imp 1) |
| `dTgt_smul` | 3 | same | yes | `CartanTargetEquivariance` :: `GroupApproximation.CharClass.dTgt_smul` (theorem, imp 2)<br>`SteenrodTargetLinear` :: `GroupApproximation.CharClass.Steenrod.dTgt_smul` (theorem, imp 1) |
| `inclMat` | 2 | same | yes | `BundleChart` :: `GroupApproximation.CharClass.Bundle.inclMat` (def, imp 1)<br>`ProjectiveSpaceHyperplane` :: `GroupApproximation.CharClass.CPn.inclMat` (def, imp 2) |
| `chartVec` | 2 | same | yes | `BundleChart` :: `GroupApproximation.CharClass.Bundle.chartVec` (def, imp 1)<br>`ProjectiveSpaceChart` :: `GroupApproximation.CharClass.CPn.chartVec` (def, imp 4) |
| `chartCP` | 2 | same | yes | `BundleChartTaut` :: `GroupApproximation.CharClass.Bundle.chartCP` (def, imp 1)<br>`LerayHirschChartClass` :: `GroupApproximation.CharClass.LH.chartCP` (def, imp 2) |
| `rankOneProj_mulVec` | 2 | same | yes | `BundleLineTriv` :: `GroupApproximation.CharClass.Bundle.rankOneProj_mulVec` (theorem, imp 4)<br>`ProjectiveSpaceHomogeneous` :: `GroupApproximation.CharClass.CPn.rankOneProj_mulVec` (theorem, imp 1) |
| `conj_rankOneProj` | 2 | same | yes | `BundleRankOne` :: `GroupApproximation.CharClass.conj_rankOneProj` (theorem, imp 1)<br>`ProjectiveSpaceHomogeneous` :: `GroupApproximation.CharClass.CPn.conj_rankOneProj` (theorem, imp 1) |
| `interHomotopyEquivSphere` | 1 | same | yes | `BundleGysinPieces` :: `GroupApproximation.CharClass.Bundle.interHomotopyEquivSphere` (def, imp 4)<br>`ProjectiveSpaceSphere` :: `GroupApproximation.CharClass.CPn.interHomotopyEquivSphere` (def, imp 1) |
| `restrictTo` | 1 | same | yes | `BundleLocal` :: `GroupApproximation.CharClass.Bundle.restrictTo` (def, imp 6)<br>`CohomologyBridge` :: `GroupApproximation.CharClass.restrictTo` (def, imp 5) |
| `pairPush` | 1 | same | yes | `CartanMidFourNat` :: `GroupApproximation.CharClass.pairPush` (def, imp 1)<br>`SteenrodDiagonalLambda` :: `GroupApproximation.CharClass.Steenrod.pairPush` (def, imp 1) |
| `mvCxInclV_comp_g` | 1 | same | yes | `CohomologyDeltaChain` :: `GroupApproximation.CharClass.MVDelta.mvCxInclV_comp_g` (theorem, imp 1)<br>`MayerVietorisPull` :: `GroupApproximation.CharClass.mvCxInclV_comp_g` (theorem, imp 2) |
| `mvResV_pull_knPrY` | 1 | same | yes | `CohomologyKunnethSurjHelp` :: `GroupApproximation.CharClass.mvResV_pull_knPrY` (theorem, imp 1)<br>`CohomologyKunnethSurjZero` :: `GroupApproximation.CharClass.KnZero.mvResV_pull_knPrY` (theorem, imp 1) |
| `component_of_mul` | 1 | same | no | `CohomologyParityKunneth` :: `GroupApproximation.CharClass.KnTwo.component_of_mul` (theorem, imp 1)<br>`SqDataInstance` :: `GroupApproximation.CharClass.Wu.component_of_mul` (theorem, imp 5) |
| `bijective_cupRight` *(structure projection)* | 1 | same | no | `GysinFromLerayHirsch` :: `GroupApproximation.CharClass.GysinData.bijective_cupRight` (theorem, imp 4)<br>`ProjectiveSpaceRing` :: `GroupApproximation.CharClass.GysinSequence.bijective_cupRight` (theorem, imp 9) |
| `continuous_chartVec` | 0 | same | yes | `BundleChart` :: `GroupApproximation.CharClass.Bundle.continuous_chartVec` (theorem, imp 1)<br>`ProjectiveSpaceChart` :: `GroupApproximation.CharClass.CPn.continuous_chartVec` (theorem, imp 4) |
| `scaleHomotopy` | 0 | same | yes | `BundleHomotopy` :: `GroupApproximation.CharClass.Bundle.scaleHomotopy` (def, imp 1)<br>`ProjectiveSpaceRetract` :: `GroupApproximation.CharClass.CPn.scaleHomotopy` (def, imp 1) |
| `instCompactSpace` *(structure projection)* | 0 | same | no | `BundleSpace` :: `GroupApproximation.CharClass.Bundle.Sphere.instCompactSpace` (instance, imp 5)<br>`BundleSpace` :: `GroupApproximation.CharClass.Bundle.Proj.instCompactSpace` (instance, imp 5)<br>`LIXBaseInstances` :: `GroupApproximation.CharClass.sphereOne.instCompactSpace` (instance, imp 3)<br>`LIXBaseInstances` :: `GroupApproximation.CharClass.unitVectorsThree.instCompactSpace` (instance, imp 3) |
| `cochain_succ` *(structure projection)* | 0 | **mixed** | no | `Cartan` :: `GroupApproximation.CharClass.NaturalHomotopy.cochain_succ` (lemma, imp 1)<br>`Cartan` :: `GroupApproximation.CharClass.DiagonalComparison.cochain_succ` (theorem, imp 1) |
| `cochain_zero` *(structure projection)* | 0 | **mixed** | no | `Cartan` :: `GroupApproximation.CharClass.NaturalHomotopy.cochain_zero` (lemma, imp 1)<br>`Cartan` :: `GroupApproximation.CharClass.DiagonalComparison.cochain_zero` (theorem, imp 1) |
| `singHom_single` | 0 | same | yes | `CartanMidFourNat` :: `GroupApproximation.CharClass.singHom_single` (theorem, imp 1)<br>`SteenrodFourfoldA` :: `GroupApproximation.CharClass.Steenrod.singHom_single` (theorem, imp 1) |
| `linearCombination_add_fun` | 0 | same | yes | `CartanSourceComplex` :: `GroupApproximation.CharClass.linearCombination_add_fun` (theorem, imp 1)<br>`SteenrodFourfoldBChainMap` :: `GroupApproximation.CharClass.Steenrod.linearCombination_add_fun` (theorem, imp 1) |
| `pushSimplex_faceSimplex` | 0 | same | yes | `CartanTargetFunctorial` :: `GroupApproximation.CharClass.pushSimplex_faceSimplex` (theorem, imp 1)<br>`SteenrodChainMapNat` :: `GroupApproximation.CharClass.Steenrod.pushSimplex_faceSimplex` (theorem, imp 3) |
| `lineEulerOf_pushforward` | 0 | same | yes | `ChernLineEulerNatural` :: `GroupApproximation.CharClass.LH.lineEulerOf_pushforward` (theorem, imp 0)<br>`SliceLineEulerPush` :: `GroupApproximation.CharClass.lineEulerOf_pushforward` (theorem, imp 0) |
| `sndMap` | 0 | **mixed** | yes | `CohomologyBridge` :: `GroupApproximation.CharClass.sndMap` (abbrev, imp 5)<br>`RelativeProdContractible` :: `GroupApproximation.CharClass.RelativeSupport.sndMap` (def, imp 1) |
| `lhDomainCard_le` | 0 | same | yes | `CohomologyLHRingPieces` :: `GroupApproximation.CharClass.LHCast.lhDomainCard_le` (theorem, imp 1)<br>`LerayHirschBridge` :: `GroupApproximation.CharClass.LH.lhDomainCard_le` (theorem, imp 3) |
| `instNonempty` *(structure projection)* | 0 | same | no | `LIXBaseInstances` :: `GroupApproximation.CharClass.sphereOne.instNonempty` (instance, imp 3)<br>`LIXBaseInstances` :: `GroupApproximation.CharClass.unitVectorsThree.instNonempty` (instance, imp 3) |
| `rank_vBundleY_lixRank` | 0 | same | yes | `LIXChernSliceValueBridge` :: `GroupApproximation.CharClass.LH.rank_vBundleY_lixRank` (theorem, imp 1)<br>`SliceSplitV` :: `GroupApproximation.CharClass.rank_vBundleY_lixRank` (theorem, imp 0) |
| `gamma_top_eq_zero` *(structure projection)* | 0 | same | no | `LemmaTwoParity` :: `GroupApproximation.CharClass.LIXParityInput.gamma_top_eq_zero` (theorem, imp 2)<br>`LemmaTwoStepD` :: `GroupApproximation.CharClass.WuStepDData.gamma_top_eq_zero` (theorem, imp 1)<br>`LemmaTwoStepDLix` :: `GroupApproximation.CharClass.WuStepDLix.gamma_top_eq_zero` (theorem, imp 2)<br>`ParityEven` :: `GroupApproximation.CharClass.ParityData.gamma_top_eq_zero` (theorem, imp 2) |
| `gamma_zero` *(structure projection)* | 0 | same | no | `LerayHirschDegree` :: `GroupApproximation.CharClass.LerayHirschGraded.gamma_zero` (theorem, imp 2)<br>`WuDiagonal` :: `GroupApproximation.CharClass.SqData.gamma_zero` (theorem, imp 1) |
| `of_linearEquiv` *(structure projection)* | 0 | same | no | `ProjectiveSpaceCohomology` :: `GroupApproximation.CharClass.HasPointCohomology.of_linearEquiv` (theorem, imp 6)<br>`ProjectiveSpaceCohomology` :: `GroupApproximation.CharClass.HasSphereCohomology.of_linearEquiv` (theorem, imp 6)<br>`ProjectiveSpaceCohomology` :: `GroupApproximation.CharClass.HasCPCohomology.of_linearEquiv` (theorem, imp 6) |
| `ne_zero_of_surjective_of_linearEquiv` | 0 | same | yes | `ThomFieldTwo` :: `GroupApproximation.CharClass.ne_zero_of_surjective_of_linearEquiv` (theorem, imp 1)<br>`ThomFieldTwo` :: `GroupApproximation.CharClass.ModuleCat.ne_zero_of_surjective_of_linearEquiv` (theorem, imp 1) |
| `congrHomotopy` *(structure projection)* | 0 | same | no | `ThomProjectivePunctured` :: `GroupApproximation.CharClass.KunnethFactor.congrHomotopy` (theorem, imp 1)<br>`ThomTopLine` :: `GroupApproximation.CharClass.HasTopLine.congrHomotopy` (theorem, imp 1) |

Four groups pair two different **kinds**: `puncturedSet` (a `def` in `Bundle`
against an `abbrev` in `CharClass`, co-open), `sndMap` (an `abbrev` against a
`def`, co-open), and `cochain_succ` and `cochain_zero` (a `lemma` against a
`theorem`, both in `Cartan`, not co-open).

Two families account for most of the co-open risk, and both are the same story as
the content duplicates in section 10.  `Bundle` against `CPn` supplies `chartSet`,
`chartVec`, `inclMat`, `continuous_chartVec`, `scaleHomotopy`,
`rankOneProj_mulVec`, `interHomotopyEquivSphere` and `cpTaut`, all co-open in
`ChernSplitRelation`; the projective space and the projective bundle were built
with one vocabulary under two namespaces.  `CharClass` against `Steenrod` supplies
`WSIndex`, `compA`, `awHom`, `dTgt_smul`, `pairPush`, `singHom_single`,
`linearCombination_add_fun` and `pushSimplex_faceSimplex`, all co-open in
`SteenrodChainMap`; that is the same `Cartan`-against-`Steenrod` wave.

`LIXChernSliceValueBridge` is `cc-projective`'s, recorded from the board at
`3f50a8dde`, batch 180; section 10's row 14 is corrected accordingly.

Nothing was edited.

## 12. Addenda to sections 10 and 11 (report only)

Both tables are a snapshot of `origin/main` at `6aa6a2b79`.  Two pairs have
appeared since, and one of them the sweep **could not** have found, which is worth
recording as a limit of the method rather than as an omission.

| A | B | owner lanes | note |
|---|---|---|---|
| `SliceVLineRoots::lineEulerOf_congr` | `SliceValueV::lineEulerOf_congr` | cc-projective / cc-steenrod | two namespaces, one name; landed after the export |
| `ParityEvenLixSplitting::exists_prod_of_two` | `SliceHomogeneous::exists_of_prod` | cc-wu / cc-steenrod | mine `7d48ef397` 07:26, theirs `5fcbaf1f8` 07:59 |
| `ParityEvenLixSplitting::exists_esymmOn_of` | `SliceHomogeneous::of_component_esymmOn` | cc-wu / cc-steenrod | same pair of files; existential form against round-trip form |

**The second and third rows are duplicates of my own work**, reported by
`cc-steenrod` against themselves.  `SliceHomogeneous` was untracked in the shared
tree when the sweep ran, so a scan of an `origin/main` export was blind to it by
construction.  That is the same hazard the fleet already records for the pre-push
duplicate scan, seen from the other end: **a sweep of `origin` cannot see a peer's
in-flight module, so its count is a lower bound and its date is part of the
result.**

On which of the two should survive, the chronology is not the argument.  Their
`exists_of_prod` is stated for an arbitrary `DecidableEq` index type while mine is
at `ℕ`, so theirs is strictly the more general statement and the better survivor
even though mine landed thirty-three minutes earlier.  Their `of_component_esymmOn`
is the round-trip form and my `exists_esymmOn_of` the existential form; each is one
line from the other.  Retirement remains the lead's call after the endpoint.

## 13. Single-consumer declarations with no transport lemma (rule 22 candidates, report only)

Export of `origin/main` at `caad23258`, 2026-09-06, all 519 modules of
`GroupApproximation/CharClass`.  A declaration is listed when it is a `def` or
`abbrev`, is used in **exactly one** module other than its own, and no declaration
in its own module or in any module importing it has a name containing `natural`,
`congr`, `comap`, `pull`, `iso`, `map`, `transport` or `restrict` while mentioning
it.  Declarations whose own names contain one of those words are skipped, being
transport lemmas themselves.

**127 candidates.**  This is a candidate list and not a verdict: the companion test
is name-based by design, so a transport lemma named otherwise reads here as absent.
The use count is deliberately generous in the other direction — the index splits
dotted paths, so a module writing `Bundle.Proj` registers a use of `Proj` — which
means a declaration reaching this list really does have at most one external
consumer.  Both errors therefore push the same way: **the list is short of the
truth, not long.**

| module | declaration | owner lane | imported by | single consumer |
|---|---|---|---|---|
| `AcyclicModels` | `acyclicModelsHomotopy` | cc-thom | 8 | `Cartan` |
| `AcyclicModels` | `homotopyOfFamily` | cc-thom | 8 | `AcyclicModelsSplitting` |
| `AcyclicModels` | `pickPreimage` | cc-thom | 8 | `AcyclicModelsExistence` |
| `CohomologyAssoc` | `degHom` | cc-cohom-api | 8 | `NeumannAlternatingFamily` |
| `CartanGroupRing` | `galEnd` | cc-cartan | 6 | `CartanTargetEquivariance` |
| `CohomologyBasic` | `cupBilin` | cc-cohom-api | 6 | `ThomChernDegreewise` |
| `CohomologySphere` | `sphereCohZeroEquiv` | cc-thom | 6 | `CohomologyShapes` |
| `LIXSectionManuscript` | `cVec` | cc-lix-odd | 6 | `LemmaTwoGlue` |
| `LemmaTwoStepCAbsEquiv` | `absEquivLix` | cc-lix-odd | 6 | `LemmaTwoStepC` |
| `MayerVietorisElement` | `mvPsi` | cc-thom | 6 | `MayerVietorisPull` |
| `BundleInvariance` | `toProjHomeo` | cc-bundle | 5 | `ChernOfInvariance` |
| `BundlePairs` | `prodPuncturedHomotopyEquivSphere` | cc-bundle | 5 | `GysinSphere` |
| `BundleSpace` | `projHomeoCP` | cc-thom | 5 | `BundleLineTriv` |
| `BundleSpace` | `projSetCP` | cc-thom | 5 | `BundleLineTriv` |
| `BundleSpace` | `tautClassifying` | cc-thom | 5 | `BundleLineTriv` |
| `CohomologyLHDegreewise` | `lhIndexEquiv` | cc-cohom-api | 5 | `CohomologyLHRestrict` |
| `BundleGysinPieces` | `chartHomeoOpens` | unattributed | 4 | `BundleChartTotal` |
| `BundleLineTriv` | `lineHom` | cc-bundle | 4 | `BundleLineIntert` |
| `BundleLineTriv` | `projTrivHomeoCP` | cc-bundle | 4 | `LerayHirschChartBundleGen` |
| `EulerLocalChart` | `chartPairHomeo` | cc-thom | 4 | `EulerLocalNonvanishing` |
| `LemmaTwoGlue` | `lixZeroPoint` | cc-lix-odd | 4 | `LemmaTwoStepC` |
| `BundleFrame` | `projFibreEquivCP` | cc-bundle | 3 | `BundleLocalOn` |
| `BundleZeroSection` | `NotZero` | cc-bundle | 3 | `BundleGysinPieces` |
| `BundleZeroSection` | `blockProj` | cc-bundle | 3 | `LanceBlockOperator` |
| `BundleZeroSection` | `projRetract` | cc-bundle | 3 | `GysinRetract` |
| `CartanComposeA` | `awTenLambda` | unattributed | 3 | `CartanEvalBasis` |
| `CartanComposeA` | `compACx` | unattributed | 3 | `SteenrodFourfoldBPackage` |
| `CartanFourfold` | `tenFreeCxHom` | unattributed | 3 | `SteenrodFourfoldA` |
| `CartanMidFourChainMap` | `midSwapHom` | unattributed | 3 | `CartanMidFourSlots` |
| `CartanTargetBoundary` | `coeffPush` | cc-cartan | 3 | `CoefficientReduction` |
| `CohomologyMayerVietoris` | `cohDualFunctor` | cc-cohom-api | 3 | `CohomologyDeltaValue` |
| `LIXThomClassTerm` | `thomJmTotal` | unattributed | 3 | `LIXThomResReduction` |
| `ParityEvenTransport` | `circHomeo` | cc-wu | 3 | `CohomologyLIXSliceBridge` |
| `ParityEvenTransport` | `splitB` | cc-wu | 3 | `LemmaTwoStepDLix` |
| `ProjectiveSpaceSymmetry` | `unitPhase` | cc-projective | 3 | `ProjectiveSpaceHomogeneous` |
| `SteenrodPairCell` | `dTgtL` | cc-steenrod | 3 | `SteenrodChainMap` |
| `SteenrodPairCell` | `dTgtR` | cc-steenrod | 3 | `SteenrodChainMap` |
| `SteenrodPairCell` | `padIdx` | cc-steenrod | 3 | `CartanEvalPair` |
| `WuSymmetric` | `esymmWuRHS` | cc-wu | 3 | `WuDiagonal` |
| `BundleOneStep` | `sumUnitEquiv` | unattributed | 2 | `BundleReindex` |
| `CartanEvaluation` | `trivialCoeff` | cc-cartan | 2 | `CartanEvalMor` |
| `CartanFreeCxTensorAug` | `tensorAug` | unattributed | 2 | `CartanFourfold` |
| `GysinFromGraded` | `colTwo` | cc-projective | 2 | `LerayHirschRankTwo` |
| `LIXCircleChart` | `circChart` | cc-lix-odd | 2 | `LIXBaseChartHomeo` |
| `LIXCircleChart` | `circChartFun` | cc-lix-odd | 2 | `LIXBaseChart` |
| `LIXCircleChart` | `circChartVec` | cc-lix-odd | 2 | `LIXBaseChart` |
| `LIXCircleChart` | `circClamp` | cc-lix-odd | 2 | `LIXBaseChart` |
| `LIXSectionChart` | `sphereChart` | cc-lix-odd | 2 | `LIXSphereChart` |
| `LIXSphereChart` | `sphereClamp` | cc-lix-odd | 2 | `LIXSphereChartHomeo` |
| `LIXVDecomposition` | `trivLine` | cc-steenrod | 2 | `LIXVLineBundles` |
| `LerayHirschChartClass` | `tautCard` | cc-projective | 2 | `GysinTautFields` |
| `LerayHirschChartClass` | `tautEmb` | cc-projective | 2 | `GysinTautFields` |
| `ParityInstance` | `parityData_of` | cc-wu | 2 | `SqDataInstance` |
| `ProjectiveSpaceCharts` | `chartOpenAt` | cc-projective | 2 | `LerayHirschUnion` |
| `ProjectiveSpaceInputs` | `chartSpace` | cc-projective | 2 | `ProjectiveSpaceComputation` |
| `RelativeCochains` | `subKeep` | cc-relative | 2 | `RelativeExcision` |
| `RelativeCochains` | `subKeepAt` | cc-relative | 2 | `RelativeExcision` |
| `RelativeCochains` | `subKeepComp` | cc-relative | 2 | `RelativeExcision` |
| `RelativeSmallChains` | `smallAnnD` | cc-thom | 2 | `CupVanishSmallAnn` |
| `SliceRoots` | `baseYFactor` | unattributed | 2 | `SliceRootsBlock` |
| `SliceRoots` | `vRoot` | unattributed | 2 | `SliceRootsBlock` |
| `SteenrodSquare` | `sqHomology` | cc-steenrod | 2 | `SteenrodTotal` |
| `ThomPuncturedPi` | `piFinSuccHomeo` | cc-thom | 2 | `LIXSectionNesting` |
| `AcyclicModelsContraction` | `ofHomotopy` | cc-thom | 1 | `AcyclicModelsTensor` |
| `AcyclicModelsResolution` | `periodicResolution` | cc-cartan | 1 | `CartanGroupRing` |
| `AcyclicModelsSplitting` | `complProj` | cc-cartan | 1 | `CartanSingularFreeCx` |
| `AcyclicModelsTensor` | `tensorPositiveContraction` | cc-cartan | 1 | `AcyclicModelsSplitting` |
| `BundleBlockIncl` | `cpBlockIncl` | cc-bundle | 1 | `BundleBlockIter` |
| `BundleChartTotal` | `chartOpensHomeoTotal` | unattributed | 1 | `ThomBridgeChart` |
| `BundleFlag` | `flagOne` | cc-bundle | 1 | `BundleFlagStage` |
| `BundleHomotopy` | `totalHomotopyEquivBase` | cc-bundle | 1 | `BundleGysinPieces` |
| `CartanEvalMor` | `fourEvalMor` | unattributed | 1 | `CartanEvalMaster` |
| `CartanEvalPre` | `fourEvalPre` | unattributed | 1 | `CartanEvalComposeB` |
| `CartanFreeCxAug` | `tsB` | unattributed | 1 | `CartanFreeCxTensorAug` |
| `CartanFreeCxAug` | `tsL` | unattributed | 1 | `CartanFreeCxTensorAug` |
| `CartanReindex` | `cartanTermL` | unattributed | 1 | `CartanFormula` |
| `CartanReindex` | `cartanTermR` | unattributed | 1 | `CartanFormula` |
| `CartanRhsSum` | `cartanRhsSum` | unattributed | 1 | `CartanFormula` |
| `CartanSingularFreeCx` | `singAug` | unattributed | 1 | `CartanFourfold` |
| `CartanSourceFunctor` | `srcFree` | cc-cartan | 1 | `CartanComparison` |
| `CartanTargetSwap` | `pairDegSwap` | cc-cartan | 1 | `CartanFreeCxSwap` |
| `CohomologyChartCover` | `chartHomotopyEquiv` | cc-cohom-api | 1 | `CohomologyProjectiveParity` |
| `CohomologyChartTowerCollapse` | `PeelFreeAt` | cc-cohom-api | 1 | `CohomologyChartFreeness` |
| `CohomologyDeltaSpec` | `eltAmb` | cc-cohom-api | 1 | `CohomologyDeltaValue` |
| `CohomologyDeltaSpec` | `eltU` | cc-cohom-api | 1 | `CohomologyDeltaValue` |
| `CohomologyDeltaSpec` | `eltV` | cc-cohom-api | 1 | `CohomologyDeltaValue` |
| `CohomologyKunnethMap` | `KunnethSecondInjective` | cc-cohom-api | 1 | `CohomologyKunnethInjective` |
| `CohomologyParityKunneth` | `chernSplit_of_noOdd` | cc-cohom-api | 1 | `ParityEvenTransport` |
| `LIXBaseBall` | `lixBallChart` | cc-lix-odd | 1 | `LIXLocalPair` |
| `LIXProductChart` | `lixProductChart` | cc-lix-odd | 1 | `LIXFullChart` |
| `LIXProjectiveChartDeriv` | `conjPiCLE` | cc-lix-odd | 1 | `LIXProductChart` |
| `LIXProjectiveChartDeriv` | `cpChartSection` | cc-lix-odd | 1 | `LIXProductChart` |
| `LIXProjectiveTowerChart` | `cpTowerChart` | cc-lix-odd | 1 | `LIXBaseChartHomeo` |
| `LIXSectionPath` | `manuscriptPath` | cc-lix-odd | 1 | `LemmaTwoZero` |
| `LIXSphereChartHomeo` | `sphereChartHomeo` | cc-lix-odd | 1 | `LIXBaseChartHomeo` |
| `LIXThomClassOfTaut` | `lixTopCoeff` | cc-lix-odd | 1 | `LIXThomClassTerm` |
| `LIXThomLH` | `lhCoeffTop` | cc-thom | 1 | `LIXThomAssembly` |
| `LemmaTwoStepDPinned` | `toWuStepDLix` | cc-lix-odd | 1 | `ParityEvenStepDClosed` |
| `LemmaTwoStepDPinned` | `toWuStepDPinned` | cc-lix-odd | 1 | `ParityEvenStepDClosed` |
| `LerayHirschPeel` | `HasPeel` | cc-projective | 1 | `LerayHirschPeelCP` |
| `ParityEvenStepDClosed` | `LixSliceValue` | cc-wu | 1 | `ParityEvenVSlice` |
| `ParityEvenStepDClosed` | `wuStepDLix_of_chernSliceValue` | cc-wu | 1 | `ParityEvenVSlice` |
| `ProjectiveSpacePerm` | `permMat` | cc-projective | 1 | `CStarKOneWhitehead` |
| `ProjectiveSpacePuncture` | `diagR` | cc-thom | 1 | `ComplexProjectivePuncture` |
| `ProjectiveSpacePuncture` | `scaleMat` | cc-thom | 1 | `ComplexProjectivePuncture` |
| `ProjectiveSpacePuncture` | `scaleVec` | cc-thom | 1 | `ComplexProjectivePuncture` |
| `ProjectiveSpaceRetract` | `scaleP` | cc-projective | 1 | `ComplexProjectivePunctureRetract` |
| `ProjectiveSpaceTwoCover` | `subtypeInterHomeo` | cc-projective | 1 | `ComplexProjectiveCover` |
| `SliceVLinesY` | `vLineYFlat` | unattributed | 1 | `SliceSplitV` |
| `SteenrodChainMap` | `phiOfS` | cc-steenrod | 1 | `SteenrodChainMapHom` |
| `SteenrodChainMap` | `phiOfW` | cc-steenrod | 1 | `SteenrodChainMapHom` |
| `SteenrodDiagonalLambda` | `PairIndex` | cc-steenrod | 1 | `SteenrodDiagonalTarget` |
| `SteenrodFourfoldBGeneric` | `genB` | unattributed | 1 | `NeumannAlternatingFamily` |
| `SteenrodPairing` | `pairEval` | cc-steenrod | 1 | `CartanEvalPair` |
| `SteenrodTargetLinear` | `dTgtLin` | cc-steenrod | 1 | `SteenrodChainMapHom` |
| `ThomBridgeChart` | `bridgeChart` | cc-thom | 1 | `ThomBridgeTotal` |
| `ThomBridgeTotal` | `bridgeTotal` | unattributed | 1 | `LIXThomClassTerm` |
| `ThomPuncturedCover` | `interOpensHomeo` | cc-thom | 1 | `ThomPuncturedRecursion` |
| `ThomPuncturedCover` | `leftOpens` | cc-thom | 1 | `ThomPuncturedRecursion` |
| `ThomPuncturedCover` | `leftOpensHomeo` | cc-thom | 1 | `ThomPuncturedRecursion` |
| `ThomPuncturedCover` | `puncturedProd` | cc-thom | 1 | `ThomPuncturedRecursion` |
| `ThomPuncturedCover` | `rightOpens` | cc-thom | 1 | `ThomPuncturedRecursion` |
| `ThomPuncturedCover` | `rightOpensHomeo` | cc-thom | 1 | `ThomPuncturedRecursion` |
| `ThomRelativeCokernel` | `relQuotEquiv` | cc-thom | 1 | `ThomSphereSubspace` |
| `ThomSphereSubspace` | `relQuotEquiv_of_sphere` | cc-thom | 1 | `ThomSectionDetect` |
| `ThomTopLine` | `CircleTopLineStep` | cc-thom | 1 | `ThomTopLineCircle` |
| `LIXSectionChartPair` | `lixChartPairHomeo` | cc-lix-odd | 0 | `ThomStepCOdd` |

The ten most-imported candidates are the top ten rows.  Two observations for
whoever annotates them.

Eight of the ten sit in modules imported by four or more others, which is the
combination rule 22 is about: a declaration widely available and used once.  That
is where a second consumer is most likely to arrive and least likely to find what
it needs.

The concentration is not uniform.  `cc-thom` and `cc-lix-odd` hold fifteen
candidate modules each and `cc-wu` four; eighteen modules carry no lane token in
their commit subjects and are marked unattributed rather than guessed.  Lane
attribution here is the leading lane token of the module's commit subjects, the
same method as section 10, and it is weaker than that section's because these
modules are older on average.

Nothing was edited and no owner was messaged.
