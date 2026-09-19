# The Hilbert-module analysis layer: Cauchy--Schwarz, `𝓛(E)`, `𝓚(E)`, and the
# cycles of `KK(A,B)`

**Authored 2026-08-19. UNCOMPILED and UNWIRED.** Seven new modules under
`GroupApproximation/Analysis/`, none imported from `GroupApproximation.lean`.

## Where this sits

`notes/TWW_KK_UCT_WAVE.md` ended with a precise obstruction list.  Hilbert
C⋆-modules and adjointable operators existed (`CStarHilbertModule`,
`CStarAdjointable`), and so did the finite-rank ideal (`CStarFiniteRank`), but
all three stopped at the same wall, recorded in each of their docstrings:

> the compact operators need a norm on the module, hence Cauchy--Schwarz for
> `B`-valued inner products, hence the order theory of `B`.

This wave goes through that wall and keeps going to the definition of a
Kasparov bimodule.

| target | before | after |
|---|---|---|
| `IsPositiveElem` vs `0 ≤ a` | two spellings, no bridge | `isPositiveElem_iff_nonneg` |
| Cauchy--Schwarz `⟨y,x⟩⟨x,y⟩ ≤ ‖⟨x,x⟩‖⟨y,y⟩` | absent | **proved** |
| the module norm, triangle inequality | absent | **proved** |
| operator norm on `𝓛(E)`, `‖T⋆‖ = ‖T‖` | absent | **proved** |
| the C⋆-identity `‖T⋆T‖ = ‖T‖²` | absent | **proved** |
| `𝓚(E)`: ideal, `⋆`-closed, norm-closed | absent | **proved** |
| direct sums `E ⊞ F`, `⨁ᵢ Eᵢ` | absent | **proved** |
| Kasparov bimodules, degenerate cycles, their direct sum | absent | **defined and verified** |
| `H_B = ℓ²(B)`, Kasparov stabilization, the product | absent | still absent |

## The modules, in dependency order

1. `Analysis/CStarPositiveOrder.lean` --- the dictionary
   `IsPositiveElem a ↔ 0 ≤ a` (mathlib's
   `CStarAlgebra.nonneg_iff_eq_star_mul_self`, available non-unitally), the two
   conjugation estimates `c⋆ac ≤ c⋆bc` and `c⋆ac ≤ ‖a‖ • c⋆c`, monotonicity of
   the norm on positives, and the parallelogram estimate
   `(a+b)⋆(a+b) ≤ 2(a⋆a + b⋆b)` --- the last one for `H_B`, not for this wave.
2. `Analysis/CStarHilbertModuleNorm.lean` --- **Cauchy--Schwarz**, in the form
   `⟨y,x⟩⟨x,y⟩ ≤ ‖⟨x,x⟩‖ • ⟨y,y⟩`, proved by testing positivity of
   `⟨x·b - ‖⟨x,x⟩‖y, ·⟩` at `b = ⟨x,y⟩`; then `‖x‖ = ‖⟨x,x⟩‖^{1/2}` with
   `norm_inner_le`, `norm_add_le`, `norm_smul`, `norm_neg`, `norm_sum_le`,
   `norm_eq_zero_iff`, and `norm_act_le : ‖x·b‖ ≤ ‖x‖‖b‖`.  `selfModule_norm`
   identifies the module norm of `B` over itself with the C⋆-norm.
3. `Analysis/CStarAdjointableNorm.lean` --- `sub`, `neg`, `map_sub`;
   `IsBoundedBy`/`IsBounded`; **`IsBoundedBy.adjoint`**, an operator and its
   adjoint obey the same bounds, proved in three lines from
   `‖T⋆y‖² = ‖⟨T(T⋆y),y⟩‖` --- *no closed graph theorem, no completeness*;
   `opNorm` as the infimum of the bounds, with the infimum proved to be a
   bound; `opNorm_adjoint`, `opNorm_comp_le`, and the **C⋆-identity**
   `‖T⋆T‖ = ‖T‖²`.
4. `Analysis/CStarCompactOperators.lean` --- `IsCompactOp`; finite ranks are
   compact; closed under sums, differences, scalars, adjoints; a **two-sided
   ideal** under composition with bounded operators; and **norm-closed**
   (`isCompactOp_of_approx`).  Plus the pointwise-invariance lemmas
   (`IsCompactOp.congr` and friends) that replace an extensionality principle
   for `Adjointable`.
5. `Analysis/CStarModuleDirectSum.lean` --- `E ⊞ F` and `⨁ᵢ Eᵢ` over a
   `Fintype`.  Definiteness of the direct-sum inner product is
   `Finset.sum_eq_zero_iff_of_nonneg`: this is the point at which the order on
   `B` stops being a convenience and becomes necessary, since without it the
   vanishing of `∑⟨xᵢ,xᵢ⟩` would say nothing about the summands.
6. `Analysis/CStarDirectSumOperators.lean` --- `norm_prod_le`, `norm_fst_le`,
   `norm_snd_le`; the inclusions `ι₁, ι₂` with the projections *defined* as
   their adjoints; `S ⊞ T`, and the theorem that a direct sum of compacts is
   compact --- proved from the ideal property through the pointwise identity
   `S ⊞ T = ι₁Sp₁ + ι₂Tp₂`.
7. `Analysis/KasparovBimodule.lean` --- `IsRepresentation` and
   **`KasparovBimodule`**: a graded module, an even representation, an odd
   operator with `(F²-1)π(a)`, `(F-F⋆)π(a)` and `[F,π(a)]` compact.  Degenerate
   cycles, and **the direct sum of two bimodules with all nine clauses
   verified** --- the addition of `KK(A,B)` before the homotopy relation.

## Design decisions that must not be "simplified" away

* **`[PartialOrder B]` and `[StarOrderedRing B]` are hypotheses, never
  instances**, exactly as in mathlib.  A Hilbert module is *defined* with no
  order on `B` (`CStarHilbertModule`, `CStarFiniteRank` carry none) and
  *normed* with one.  Do not add a global instance: mathlib deliberately does
  not, since a type may already carry an unrelated order.
* **Boundedness is a hypothesis, not a theorem.**  Adjointable operators on a
  Hilbert module are bounded, but the proof is the closed graph theorem and
  needs completeness of the module, which a bundled `CStarModule` is not asked
  to have.  Every operator this development builds is proved bounded with an
  explicit constant instead; nothing is lost and the completeness hypothesis
  never has to be carried.
* **Everything is pointwise.**  `IsBoundedBy`, `IsFiniteRank`, `IsCompactOp`
  and every clause of `IsRepresentation` speak about `T.toFun`.  This is what
  lets the direct-sum bimodule discharge its compactness clauses with `rfl`,
  and it is why no extensionality principle for `Adjointable` --- hence no
  appeal to proof irrelevance on its adjoint-relation field --- appears
  anywhere.
* **`opNorm` is an infimum of bounds, not a supremum over the unit ball.**
  The supremum needs boundedness to exist at all; the infimum is total, so
  `opNorm_nonneg` is unconditional and every statement with content carries
  `IsBounded` visibly.  This is mathlib's discipline for
  `ContinuousLinearMap.opNorm`.
* **Nothing here inhabits `KasparovTheory`.**  `KasparovBimodule` is the
  *cycle* type.  `KK(A,B)` is cycles modulo homotopy, and the group structure
  needs the inverse, which needs Kasparov's stabilization theorem, which needs
  `H_B`.  Claiming otherwise would be false, and the axiomatization in
  `Analysis/KKTheoryKasparov.lean` stays exactly as it was.

## One stale name repaired

`CStarHilbertModule.lean:112` and `CStarAdjointable.lean:97` called
`self_eq_add_left`, which does not exist at the pinned mathlib
(`905b9581`, v4.32.2); the current name is `left_eq_add` (the `to_additive` of
`left_eq_mul`).  Both were fixed.  Every mathlib name used in this wave was
checked against the pinned tree rather than against memory.

## Second batch: `H_B`, unitaries, and half of stabilization

Three further modules, same status (uncompiled, unwired).

8. `Analysis/CStarStandardModule.lean` --- **`H_B = ℓ²(B)`**.  Two analytic
   facts carry it, and both are proved: *domination* (a family of positive
   elements dominated by a summable one is summable --- proved by the Cauchy
   criterion on finite subsets, since a summable family of positives in a
   C⋆-algebra need not be absolutely summable, `eᵢ/i` in `c₀` being the
   counterexample), and *cross terms* (`∑fᵢ⋆gᵢ` converges when `∑fᵢ⋆fᵢ` and
   `∑gᵢ⋆gᵢ` do --- Cauchy--Schwarz in `B^s`, one finite subset at a time,
   which is why the `Fintype` direct sum is proved before the infinite one).
   The square-summable sequences are built as a `ℂ`-submodule of `ι → B`, so
   the linear structure is inherited; definiteness is `le_hasSum`.
9. `Analysis/CStarUnitary.lean` --- `IsUnitaryAdj`, with the inner product
   *proved* preserved rather than assumed (`⟨Ux,Uy⟩ = ⟨x,U⋆Uy⟩`), hence
   isometry and boundedness for free, and the groupoid structure.
10. `Analysis/CStarStandardModuleEquiv.lean` --- re-indexing along `ι ≃ κ`
    (unconditional summability is exactly what makes this legitimate), the
    merge `H_B(ι) ⊞ H_B(κ) ≅ H_B(ι ⊕ κ)`, and their composite with
    `ℕ ⊕ ℕ ≃ ℕ`: **`H_B ⊞ H_B ≅ H_B`**.  That is the case `E = H_B` of
    Kasparov's stabilization theorem --- the case that is bookkeeping.  What
    is left of stabilization is the case of a general countably generated `E`,
    which is the Mingo--Phillips argument and is not re-indexing.

## Third batch: the multiplier algebra, and `𝓚(B_B) = B`

11. `Analysis/KasparovUnitaryEquivalence.lean` --- `UnitaryEquiv` of Kasparov
    bimodules (reflexive, symmetric, transitive), the structural unitaries of a
    direct sum, and `⊞` commutative and associative **up to unitary
    equivalence**.  What is deliberately not claimed: that a degenerate cycle
    is a unit.  It is one only up to *homotopy* --- `M ⊞ (degenerate)` has a
    strictly bigger module --- and that is one of the two places the homotopy
    relation does real work, the other being the inverse.
12. `Analysis/CStarStabilization.lean` --- truncation in `H_B`: **the finitely
    supported sequences are dense**, proved from the Cauchy criterion plus the
    passage of a bound to the limit.  Then `IsCountablyGenerated`, and
    Kasparov's stabilization theorem stated as an input, with the case
    `E = H_B` recorded as already proved so that the input names exactly the
    missing passage.
13. `Analysis/CStarCompactSelfModule.lean` --- **`𝓚(B_B) = B`** and
    **`B ⊆ M(B)` isometrically**.  Three ingredients: `‖bx‖ ≤ K‖x‖` for all `x`
    forces `‖b‖ ≤ K` (test at `x = b⋆`; a C⋆-fact, false in a Banach algebra);
    a finite-rank operator on `B` is `ofElem (∑ xᵢyᵢ⋆)`; and every `ofElem b`
    is compact, which for non-unital `B` needs an approximate unit ---
    `ofElem (be) = θ_{b,e⋆}` and `be → b`.  The converse is a completeness
    argument, the isometry making the approximants Cauchy in `B`.

    Together these say `M(B) = 𝓛(𝓚(B))` in the case `E = B`, which is the case
    the Winter--Zacharias factorization of `Analysis.CStarOrderZeroSupport` is
    stated over.

## What is next, and what it costs

1. ~~`H_B = ℓ²(B)`~~ --- **done**, in the second batch above.
2. **Kasparov stabilization** `H_B ⊕ E ≅ H_B` for countably generated `E`.
   Mingo--Phillips.  This is a real theorem and the first genuine obstruction
   in the chain.
3. **The Kasparov product.**  The technical theorem.  Not reachable by adding
   files, and this note does not pretend otherwise.

Items 2 and 3 are where `KK(A,B)`, hence the UCT, hence Tikuisis--White--Winter
stops being a matter of writing down definitions.
