# cc-wu

Owns `GroupApproximation/CharClass/Wu*.lean` and `CharClass/ParityEven*.lean`.
This session continued a terminated Opus session; the four owned files were
already fully authored (mathematically complete, matching the winning
`§12.3` route of `research/artifacts/stw59-obstruction-lean-routes-2026-09-05.md`,
which supersedes the power-of-two induction of `§9`) but had never been
probed together. This session probed them, found and fixed four Lean bugs,
and landed the result.

## 1. GREEN

All four owned modules, built together:

* `GroupApproximation.CharClass.WuSymmetric`
* `GroupApproximation.CharClass.WuDiagonal`
* `GroupApproximation.CharClass.ParityEvenSlice`
* `GroupApproximation.CharClass.ParityEven`

`Build completed successfully (1553 jobs)`, commit `a411945c8`.

Deliverables, all landed and green:

1. **The `MvPolynomial` half-antidiagonal identity** (`WuSymmetric.lean`,
   `esymm_halfAntidiagonal_mvPolynomial`) — exactly the routes-doc §10.3
   statement, proved by induction on the index set (both sides obey the same
   recursion under adjoining a variable), not by the generating-function
   halving route the doc suggested (that route needs a division step in
   `ℤ[y]`; the induction avoids it). Also delivers the full-antidiagonal
   vanishing in odd degree (`esymm_antidiagonal_odd_eq_zero_mvPolynomial`)
   and `esymmWuRHS_eq_sum_powersetCard_succ`, the pair-indexed form the
   Steenrod computation produces.
2. **(Wu-diag)** (`WuDiagonal.lean`, `SqData.wu_diagonal`) — proved over an
   abstract `SqData` structure (commutative ring of characteristic two, `Sq`
   additive with `Sq^0 = id` and Cartan, a finite family of degree-two roots
   with `Sq^1 y = 0`, `Sq^2 y = y²`, `Sq^{≥3} y = 0`). The instability axiom
   is used only in this specialized form, so it isn't a separate field.
3. **Step D, the even side** (`ParityEven.lean` + `ParityEvenSlice.lean`,
   `ParityData.gamma_top_eq_zero` / `gamma_top_eq_zero_of_slice`) — proved
   over an element-level `ParityData R H` structure. **This uses the general
   "every `d_j` even" route (§12.3 of the routes doc), not the "every `d_j`
   a power of two" route of §9** that `notes/LIX_FULL_PROGRAM_2026-09-05.md`
   §4's design note describes: the mechanism here never restricts to a
   sub-product, so it needs only that the slice class `a` is supported in
   even indices and `a_0 = 1` — both of which hold for any even `d_j`, not
   just powers of two. This is confirmed correct and cheaper by the routes
   doc's own §12.3/§12.4 verdict ("Formalize §12.3... needs neither [powers
   of two nor restriction maps] and is four lines"). Documented in both
   files' module docstrings.

## 2. AUTHORED, UNVERIFIED

Nothing. All owned deliverables are green.

## 3. NEEDS

Nothing outstanding from peers. `cc-lix-odd`'s report (§"From `cc-wu`") asked
that the `ParityData` interface stay **element-level** (a type `H` with `+`,
`*`, a Künneth decomposition via an explicit ring map `ι : R →+* H`, `Sq`,
and the listed identities) rather than a bundled `GradedAlgebra`, so it can
be fed by `cc-cohom-api`'s `cohomologyZMod2` API through explicit ring maps.
**This is exactly the shape `ParityData` already has** — no change needed.

The exact `ParityData` fields to instantiate, for `cc-lix-odd` and
`cc-projective`:

```lean
structure ParityData (R H : Type*) [CommRing R] [CommRing H] where
  two_eq_zero : (2 : R) = 0
  ι : R →+* H                              -- H^*(Y) → H^*(N), Künneth inclusion
  t x : H                                  -- degree-1 (S¹) and degree-5 (S⁵) generators
  t_mul_t : t * t = 0
  tx_inj : ∀ u v : R, ι u + t * x * ι v = 0 → v = 0   -- Künneth uniqueness
  SqH : ℕ → H →+ H
  SqR : ℕ → R →+ R
  sqH_zero_apply : ∀ c : H, SqH 0 c = c
  cartanH : ∀ (n : ℕ) (u v : H), SqH n (u * v) = ∑ p ∈ Finset.range (n + 1), SqH p u * SqH (n - p) v
  sqH_t : ∀ n : ℕ, 0 < n → SqH n t = 0
  sqH_x : ∀ n : ℕ, 0 < n → SqH n x = 0
  sqH_ι : ∀ (n : ℕ) (r : R), SqH n (ι r) = ι (SqR n r)
  γ : ℕ → H                                -- mod-2 Chern classes of the bundle W
  a b : ℕ → R                              -- Künneth components: γ k = ι (a k) + t * x * ι (b k)
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + t * x * ι (b k)
  a_zero : a 0 = 1
  a_odd : ∀ q : ℕ, Odd q → a q = 0         -- Frobenius evenness of the slice class
  sq_b : ∀ k j : ℕ, 2 * k < j + 6 → SqR j (b k) = 0   -- instability, in the only form used
  wu : ∀ i : ℕ, SqH (2 * i) (γ (i + 1)) = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)
```

The two consumable endpoints:

```lean
theorem ParityData.gamma_top_eq_zero {m : ℕ} (hm : Even m)
    (ha : ∀ q : ℕ, m < q → P.a q = 0) : P.γ (m + 3) = 0

theorem ParityData.gamma_top_eq_zero_of_slice {J : Type*} (u : Finset J) (h : J → R) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, P.a q = (sliceClass u h d).coeff q) :
    P.γ ((∑ j ∈ u, d j) + 3) = 0
```

`sliceClass u h d : Polynomial R` (`ParityEvenSlice.lean`) packages
`∏_j (1 + h_j)^{d_j}` with its `q`-th coefficient being the degree-`2q`
component; only `Even (d j)` is required, not "power of two".

To instantiate: supply `H := cohomologyZMod2 N`, `R := cohomologyZMod2 Y`,
`ι` from `cc-cohom-api`'s pullback along `Y ↪ N` (basepoint inclusion at
`t = x = 0`), `t, x` the pullbacks of the `S¹`/`S⁵` generators, `SqH`/`SqR`
from `cc-steenrod`, and `γ` from `cc-projective`'s mod-2 Chern classes of
`W`/`p^*V`. `a`, `b` are then *defined* (not further hypothesized) as the
Künneth components of `γ`, which requires `cc-cohom-api`'s Künneth splitting
`H^{even}(N) = H_Y ⊕ tx·H_Y` to produce `tx_inj` and the projections
supplying `a`/`b`.

## 4. TRAPS

* **`rw [Finset.sum_range_reflect]` (or any lemma whose LHS pattern is
  `?f (?n - 1 - j)`) fails through an unreduced beta-redex.** If the sum's
  summand was produced by `Finset.sum_congr rfl key` with `key`'s RHS stated
  as `(fun q => body) (shift j)` (left as an explicit lambda application
  rather than beta-reduced), `rw` cannot unify the metavariable-headed
  pattern `?f (?n - 1 - j)` against it — `kabstract` apparently reduces the
  redex before matching, at which point there is no longer a literal
  application for `?f` to bind to, and inverting a compound argument like
  `i + 1 - 1 - j` out of the reduced expression is not a Miller pattern.
  Fix: never leave the shifted form as a bare `(fun q => ...) (arg)`; either
  state the target of a `show ... from (lemma args).symm` ascription with
  the shift **already beta-reduced** (elaboration's `isDefEq` handles beta
  freely, unlike `rw`'s syntactic matching) and finish with a pointwise
  `Finset.sum_congr` + `omega`-driven index rewrites, or close the sum
  equality with a direct `exact lemma_with_explicit_args` rather than `rw`.
  Hit twice (`WuSymmetric.esymmHalf_eq_sum_sub`, `ParityEven.sum_a_mul_b_eq_zero`'s
  `hB1`); same fix both times.
* **A `theorem` inside a `variable (P : Foo)` section that doesn't mention
  `P` in its *stated type* does not get `P` bound**, even though the proof
  body uses `P` freely and even though later declarations in the same
  section do get `P` auto-included. The error surfaces as "unknown
  identifier `P.field`" *inside the proof*, plus (at every downstream call
  site written as `P.thatLemma`) "Invalid field notation: does not have a
  usable parameter of type `Foo`". Fix: give the theorem an explicit `(P :
  Foo)` binder in its own signature, shadowing the ambient `variable`.
* **`map_ofNat` (`RingHom`/`MonoidHom` applied to a numeral `≥ 2`) is
  deliberately not `@[simp]`** (documented in Mathlib as a discrimination-tree
  performance tradeoff: its LHS key would just be `DFunLike.coe`). A bare
  `simp` proving `(2 : H) = f 2` or similar silently fails ("no progress");
  use `(map_ofNat f 2).symm` or add it explicitly to the `simp` set.
* **`Polynomial.eval_prod` and `Polynomial.natDegree_X_le` are not
  `@[simp]`** either (the latter because the equality version `natDegree_X`
  needs `[Nontrivial R]` and this file works over a general `CommRing`; the
  unconditional inequality lives in the general `Semiring` section under a
  different, non-simp name). A bare `simp` after unfolding a product/degree
  goal reports "no progress" or leaves an unsolved inequality; name the
  lemma explicitly.
* **A duplicated `rw` item that already had no more work to do fails, not
  no-ops.** `rw [map_zero, map_zero, ...]` errors on the second `map_zero`
  once the first already rewrote every syntactically-identical occurrence of
  `f 0` in one pass (`kabstract` abstracts all matching occurrences of the
  *same instantiation* together, not just the first). If a rewrite target
  might have two occurrences of the same pattern, one call handles both;
  listing it twice is not defensive, it is a guaranteed later failure.
* General note for the next lane touching this material: probe early. All
  four bugs above were latent since the file was authored (predecessor's
  session ended before a first probe); none were visible from re-reading the
  source, all four were one-line-context obvious once the actual Lean error
  was in hand.
