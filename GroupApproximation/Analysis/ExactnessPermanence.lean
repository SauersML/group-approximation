import GroupApproximation.Sofic.CliffordLampPermanence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# Exactness permanence: what the manuscript's chain needs, and what is proved

## The manuscript's chain

Locate the passage in `non_mf_groups_exist.tex` by the string
`\paragraph{An exact stably finite non-MF algebra.}` --- line numbers drift.
It deduces exactness of `Cred(W)` for the Clifford witness
`W = ClLamp(X) ⋊ V` in four links, numbered `E.1`--`E.4` throughout:

| link | manuscript step | external input | side |
|---|---|---|---|
| `E.1` | the locally finite lamp kernel `ClLamp(X)` is amenable, hence exact | folklore, uncited | group |
| `E.2` | the linear group `V ≤ GL₄(ℚ)` is exact | `\cite{GHW}` | group |
| `E.3` | exact groups are closed under extensions, so `W` is exact | `\cite{KWPermanence}` | group |
| `E.4` | for a discrete group, `W` exact ⟺ `Cred(W)` exact | `\cite{KWExact}` | crossover |

`GHW` = Guentner--Higson--Weinberger, *The Novikov conjecture for linear
groups*, Publ. IHES **101** (2005) 243--268.
`KWPermanence` = Kirchberg--Wassermann, *Permanence properties of C⋆-exact
groups*, Doc. Math. **4** (1999) 513--558.
`KWExact` = Kirchberg--Wassermann, *Exact groups and continuous bundles of
C⋆-algebras*, Math. Ann. **315** (1999) 169--203.

The manuscript flags the gap itself: *"All parts of this paragraph except
exactness are also verified in Lean; the present formal library has no
definition of exact C⋆-algebras."*  That sentence is **accurate** and should
stand.

## The group / C⋆ split

`E.1`--`E.3` are assertions about exactness *of groups*.  For a countable
discrete group, group exactness is Yu's **property A** (Higson--Roe, Ozawa):
a purely combinatorial condition --- finitely supported probability measures
moving slowly in `ℓ¹` along bounded translations --- which needs no operator
algebra, no tensor product, and no functional analysis whatsoever.  That is
`HasPropertyA` below, and it is why the group half of the chain is approachable
at all.

Only `E.4` crosses from groups to algebras, and `E.4` is precisely the link
that hits the missing foundations: exactness of a C⋆-algebra is *defined* by
the behaviour of `A ⊗_min ·`, and Mathlib has no **C⋆-norm** on a tensor
product --- although, as the survey in `CStarExactness.lean` records with
file/line evidence, it does have the algebraic tensor product as a ⋆-algebra,
the Hilbert cross norm, the operator tensor `mapL`, and completions of inner
product spaces.  The gap is the C⋆-norms, not the scaffolding.  `E.4`
therefore depends on the peer C⋆-tensor modules, and is deliberately not
attempted here.

## What this file proves

* `hasPropertyA_of_isLocallyFiniteGroup`: **a locally finite group has property
  A**.  The finite scale `R` sits inside a finite subgroup `H`; the uniform
  measure on the coset `g·H` is *exactly* invariant under moving the base point
  inside `H`, so the `ℓ¹` defect is `0` and no limit is taken.
* `GroupApproximation.ExactnessPermanence.hasPropertyA_cliffordLamp_viaAmenability`: the manuscript's actual lamp kernel
  `ClLamp(X)` has property A, for every site set `X`.  This is the
  group-combinatorial content of `E.1`, discharged on the real object.
* `hasPropertyA_of_finite`: the degenerate case.
* `PropertyAWitness.exists_window`, `PropertyAWitness.sum_window_eq`: the `ℓ¹`
  clause of the definition is neither vacuous nor window-dependent.
* `HasAlmostInvariantWeights` (amenability in Day's `ℓ¹` form),
  `hasAlmostInvariantWeights_of_isLocallyFiniteGroup` and
  `hasPropertyA_of_hasAlmostInvariantWeights`: **amenable `⟹` property A**,
  so that `E.1` can be run through the manuscript's own intermediate object.
  `hasPropertyA_cliffordLamp_viaAmenability` is the lamp kernel along that
  route: locally finite `⟹` amenable `⟹` property A.

## Status of each link, honestly

* **`E.1` --- group side closed, crossover open.**  The whole group-level
  content is proved, on the manuscript's own lamp group, and along the
  manuscript's own route: locally finite `⟹` amenable `⟹` property A
  (`hasPropertyA_cliffordLamp_viaAmenability`).  Amenability is used in Day's
  `ℓ¹` form; its equivalence with the invariant-mean form already in this
  repository (`Amenability.IsAmenable`) is Day's theorem and is not formalized,
  so the two amenability notions live side by side rather than being
  identified.  The remaining gap in `E.1` is the crossover
  `property A ⟹ Cred exact`, which is Ozawa's theorem.
* **`E.2` --- MISSING, research-scale.**  Property A for linear groups is the
  main theorem of `GHW`; the proof runs through actions on products of affine
  buildings over the locally compact completions of a finitely generated field.
  Nothing in that toolkit exists in Mathlib.
* **`E.3` --- CLOSED**, in `Analysis/PropertyAExtension.lean`
  (`hasPropertyA_of_ker_of_quotient`), together with the semidirect-product form
  the manuscript actually uses
  (`hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup`).

  This corrects an assessment that stood here previously, and the correction is
  worth stating because the earlier reasoning was specific and wrong.  It ran:
  the naive fibre-wise proof fails, because a set-theoretic section
  `σ : G/N → G` has `σ(q)σ(q')⁻¹` unbounded, so fibre base points cannot be
  compared uniformly; hence coarse geometry --- word metrics and a
  quasi-isometric section --- is needed.

  The unboundedness is real but is never invoked, because base points are only
  ever compared **within a single fibre**, and there the section value cancels.
  With base point `n(g,q) = σ(q)⁻¹ g σ(π(g)⁻¹q)` one has

  ```
      n(g,q)⁻¹ n(h,q) = σ(π(g)⁻¹q)⁻¹ (g⁻¹h) σ(π(h)⁻¹q) ,
  ```

  in which `σ(q)` has disappeared; the surviving section values are taken at
  arguments running over the *finite* template of the quotient witness, so only
  finitely many of them are ever compared.  No metric enters, and the
  prerequisite G1 below is not needed for `E.3` after all.  (The corresponding
  statement for general bounded-geometry metric spaces is subtler; what makes
  the group case go through is that the support constraint in
  `PropertyAWitness` is `g`-relative.)
* **`E.4` --- MISSING, and not statable today.**  The obstruction is precise:
  Mathlib has no C⋆-norm on a tensor product, so `A ⊗_min ·` does not exist and
  exactness cannot be written down.  Owned by the peer C⋆-tensor modules.

## Engineering assessment, split by side

Sizes are Mathlib-scale estimates for a from-scratch build against the pinned
revision, which has none of the following.

### Tier G --- group side, needs no tensor products

* **G1. Coarse geometry for finitely generated groups.**  Prerequisite for
  anything beyond `E.1`.  **Partly built already**: `Algebra/WordMetric.lean`
  now supplies `wordNorm` with subadditivity (`wordNorm_mul_le`),
  `wordNorm_inv`, `wordNorm_mono`, a shortest-word witness
  (`exists_isWord_length_eq`), and `wordDist` with `wordDist_comm`,
  `wordDist_triangle`, `wordDist_left_invariant` and `wordDist_eq_zero_iff`,
  all under `IsSymmetricGeneratingSet`.  That is the generic half.  What is
  still missing is specifically the finite-generation and quotient half, and
  it is exactly the machinery `E.3`'s obstruction turns on:
  1. **Finite balls.** `{g | wordNorm S g ≤ n}` is finite for finite `S`.
     `WordMetric.lean` is deliberately general (`S` may be infinite and need
     not contain `1`), so this is not there.  *~150 lines.*
  2. **Quotient word metric and geodesic lifting.**  `wordNorm (π '' S) (π g) ≤
     wordNorm S g` by pushing `IsWord` forward, and then a section `σ` built by
     lifting a shortest word letter by letter, giving `|σ q|_S ≤ |q|_{π '' S}`.
     This is the quasi-isometric section, and it is the step that repairs the
     unbounded-`σ(q)σ(q')⁻¹` failure described above.  *~300 lines.*
  3. **Scale bridge.**  `HasPropertyA` here is indexed by a `Finset` scale;
     the coarse proof is indexed by ball radii.  For finitely generated groups
     these agree (a `Finset` sits in a ball, a ball is a `Finset` by (1)), but
     the translation has to be written.  *~150 lines.*

  So the prerequisite is now *~600 lines* rather than ~800, and --- more
  usefully --- its content is three named items rather than "coarse geometry".
* **G2. DONE here.**  Amenability in Day's `ℓ¹` form, and `amenable ⟹ property
  A`.  What is *not* done, and is the residue of G2, is Day's theorem
  (invariant mean `⟹` almost invariant weights) and the Følner-set form; those
  would identify `HasAlmostInvariantWeights` with the repository's existing
  `Amenability.IsAmenable`.  *~500 lines* for the residue.
* **G3. Property A permanence: subgroups, direct products, increasing unions.**
  Subgroup heredity is the next thing to build, and the recipe below is fully
  worked out and name-verified against the pinned Mathlib, so it can be picked
  up cold.  For `H ≤ G` with `HasPropertyA G`, at scale `R : Finset H`:
  take the `G`-witness at scale `R.image (↑· : H → G)`, with template `S` and
  weights `μ`, and push forward along the transversal retraction
  `GroupApproximation.Amenability.retract H : G → H`, which this repository
  already provides together with the equivariance
  `retract_mul_left : retract H (↑k * g) = k * retract H g`.  Set

  ```
  template := S.image (Amenability.retract H)
  weight k y := ∑ s ∈ S with Amenability.retract H s = k⁻¹ * y, μ ↑k (↑k * s)
  ```

  The five steps and the lemmas each needs:
  1. `weight_eq_zero`: the filter is empty, so `Finset.sum_eq_zero` closes it
     vacuously from `Finset.mem_filter`.
  2. `weight_sum`: `inv_mul_cancel_left` normalises the predicate, then
     `Finset.sum_fiberwise_of_maps_to`
     (`(h : ∀ i ∈ s, g i ∈ t) (f) : ∑ j ∈ t, ∑ i ∈ s with g i = j, f i =
     ∑ i ∈ s, f i`) collapses the fibres onto `W.weight_sum`.
  3. `weight_close`, window change: rewrite the `S`-filter form as a filter over
     the translated window `↑k • S` (`Finset.sum_image`), then enlarge to the
     common window `U := (↑k • S) ∪ (↑l • S)` by `Finset.sum_subset`, using that
     `μ` vanishes off its own window.
  4. `weight_close`, contraction: `Finset.abs_sum_le_sum_abs` fibrewise, then
     `Finset.sum_fiberwise_of_maps_to` again, landing on `W.weight_close` with
     window `U`.
  5. `weight_close`, window extension: `Finset.sum_subset` from
     `U.image (retract H)` out to the arbitrary `T`.

  *~300 lines.*  Deliberately not written here: it is five interlocking
  `Finset` reindexings, and this session cannot compile, so landing it would put
  the finished `E.1` result in this file at risk for a lemma that is not itself
  on the `E.1`--`E.3` chain.
* **G4. DONE**, in `Analysis/PropertyAExtension.lean`, and without G1: `~450`
  lines rather than the `~2000` estimated here, because the fibre-wise proof
  does work (see the corrected `E.3` entry above).  The reusable by-products
  are `PropertyAWitness.sum_le_one`, `PropertyAWitness.sum_abs_sub_le` and
  `HasPropertyA.of_mulEquiv`.
* **G5. `E.2`: linear groups have property A.**  Research-scale; not
  recommended.

### Tier A --- algebra side, blocked on the missing C⋆-tensor norms

The block is narrower than "Mathlib has nothing".  Mathlib already has the
algebraic tensor product as a ⋆-algebra (`Algebra R (A ⊗[R] B)`,
`StarRing (A ⊗[R] B)`, `star_tmul`), the inner product space
`E ⊗[𝕜] F` with the multiplicative cross norm (`norm_tmul`), the operator
tensor `ContinuousLinearMap.mapL` with `norm_mapL_le` and `mapL_mul`, and
`Completion.innerProductSpace`.  What is absent is the *C⋆-norms* on a tensor
product --- and hence nuclearity and exactness.  See the survey in
`CStarExactness.lean` for file/line evidence.

Items A1--A3 are **owned by the peer C⋆-tensor lane**
(`Analysis/CStarTensorProduct.lean` and its `Adjointable` and `Seminorm`
modules, with the maximal norm and nuclearity queued behind them); the
estimates are recorded here only so that the `E.4` dependency is visible, not
as work to be duplicated.  That lane's roadmap in turn defers the exactness
and nuclearity rows to this file and to `CStarExactness.lean`, so the two
accountings are complements, not duplicates: A1--A3 there, A4--A7 here.  The
two lanes agree on the verdict.

* **A1. Hilbert space tensor product `H ⊗̂ K`.**  `Completion (H ⊗[ℂ] K)`
  carries an `InnerProductSpace`; the work is extending `mapL f g` continuously
  to the completion, showing the extension is multiplicative and adjoint
  preserving, and upgrading `norm_mapL_le` to `‖S ⊗̂ T‖ = ‖S‖ * ‖T‖`.
  *~500 lines* --- much less than a from-scratch estimate would suggest.
* **A2. Spatial tensor product of concretely represented C⋆-algebras**: the
  closed ⋆-subalgebra of `B(H ⊗̂ K)` generated by elementary tensors.  Given A1
  and the existing `StarRing (A ⊗[ℂ] B)`, this is mostly assembly.
  *~400 lines.*
* **A3. Independence of the spatial norm from the chosen faithful
  representations** (Takesaki).  What makes `⊗_min` well defined; needs states,
  GNS (Mathlib has `GelfandNaimarkSegal`), and a slice-map argument.  Genuinely
  hard and *not* helped by the existing scaffolding.  *~3000 lines.*
* **A4. Quotients of C⋆-algebras.**  `B/J` for a closed two-sided ideal is a
  C⋆-algebra.  Mathlib's `Ideal.Quotient.semiNormedCommRing` and
  `normedCommRing` are *commutative only*, so even the seminormed quotient ring
  has to be redone noncommutatively; the C⋆-identity on the quotient then needs
  an approximate unit of `J` (Mathlib has `CStarAlgebra.ApproximateUnit`).
  Without A4 one cannot even *state* exactness.  *~1200 lines.*
* **A5. The definition of C⋆-exactness** and its elementary permanence.
  *~400 lines* given A1--A4.
* **A6. Kirchberg's theorem** (`exact ↔ nuclearly embeddable`, separable case),
  connecting `IsNuclearlyEmbeddable` in `CStarExactness.lean` to A5.
  Research-scale.
* **A7. `E.4` proper**, plus Ozawa/Higson--Roe `property A ⟹ Cred exact`:
  needs the uniform Roe algebra, amenable actions on compact spaces, and
  nuclearity of crossed products --- and Mathlib has no crossed products.
  Research-scale.

A1--A5 are what it takes to make the *statement* of the manuscript's claim
expressible at all; A6, A7 and G5 are what it takes to *prove* it (G4 is now
done).  The realistic verdict is unchanged --- the exactness row is out of
reach for this development, because `E.4` is not statable and `E.2` is
research-scale --- but the group side of the chain is now complete except for
`E.2`.  The remaining reachable increments, in order of value, are G3, then G1,
then the residue of G2; none of them is on the `E.1`--`E.4` chain.
-/

namespace GroupApproximation
namespace ExactnessPermanence

universe u

/-! ## Property A for a discrete group -/

/-- A single witness for Yu's **property A** of a discrete group `G`, at scale
`R` and tolerance `ε`.

`weight g` is a finitely supported probability measure on `G`, attached to the
point `g`, and living inside the translate `g · template` of a single finite
`template`.  The requirement is that these measures move slowly in `ℓ¹` when
the base point is translated by an element of the scale `R`.

The `ℓ¹` distance is expressed as a sum over an arbitrary finite `T` containing
both supports.  This is exactly the `ℓ¹` norm of the difference: any two such
`T` give the same sum (`sum_window_eq`), and at least one such `T` always
exists (`exists_window`), so the condition is neither ambiguous nor vacuous.
Phrasing it this way avoids a `DecidableEq G` side condition in the definition
itself. -/
structure PropertyAWitness (G : Type u) [Group G] (R : Finset G) (ε : ℝ) where
  /-- The finite template; the measure at `g` lives on `g · template`. -/
  template : Finset G
  /-- `weight g x` is the mass that the measure attached to `g` puts on `x`. -/
  weight : G → G → ℝ
  /-- The measures are nonnegative. -/
  weight_nonneg : ∀ g x, 0 ≤ weight g x
  /-- The measure attached to `g` is supported inside `g · template`. -/
  weight_eq_zero : ∀ g x, g⁻¹ * x ∉ template → weight g x = 0
  /-- Each measure has total mass one. -/
  weight_sum : ∀ g, ∑ s ∈ template, weight g (g * s) = 1
  /-- Base points at distance at most `R` carry measures at `ℓ¹` distance at
  most `ε`. -/
  weight_close : ∀ g h, g⁻¹ * h ∈ R → ∀ T : Finset G,
    (∀ x, weight g x ≠ 0 → x ∈ T) → (∀ x, weight h x ≠ 0 → x ∈ T) →
      ∑ x ∈ T, |weight g x - weight h x| ≤ ε

/-- **Yu's property A** for a discrete group: at every finite scale and every
positive tolerance there is a system of slowly varying finitely supported
probability measures.

For a countable discrete group this is equivalent, by Ozawa's theorem, to
exactness of `Cred(G)`.  That equivalence is *not* formalized; see the module
docstring. -/
def HasPropertyA (G : Type u) [Group G] : Prop :=
  ∀ (R : Finset G) (ε : ℝ), 0 < ε → Nonempty (PropertyAWitness G R ε)

namespace PropertyAWitness

variable {G : Type u} [Group G] {R : Finset G} {ε : ℝ}

/-- A finite set containing the supports of both measures always exists, so the
`ℓ¹` clause of `PropertyAWitness` is not vacuous. -/
theorem exists_window (W : PropertyAWitness G R ε) (g h : G) :
    ∃ T : Finset G, (∀ x, W.weight g x ≠ 0 → x ∈ T) ∧
      (∀ x, W.weight h x ≠ 0 → x ∈ T) := by
  classical
  refine ⟨W.template.image (fun s ↦ g * s) ∪ W.template.image (fun s ↦ h * s),
    ?_, ?_⟩
  · intro x hx
    have hmem : g⁻¹ * x ∈ W.template := by
      by_contra hcon
      exact hx (W.weight_eq_zero g x hcon)
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g⁻¹ * x, hmem, ?_⟩)
    exact mul_inv_cancel_left g x
  · intro x hx
    have hmem : h⁻¹ * x ∈ W.template := by
      by_contra hcon
      exact hx (W.weight_eq_zero h x hcon)
    refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨h⁻¹ * x, hmem, ?_⟩)
    exact mul_inv_cancel_left h x

/-- The `ℓ¹` sum does not depend on which containing finite set it is taken
over, so the quantifier over `T` in `weight_close` really does express the `ℓ¹`
norm of the difference. -/
theorem sum_window_eq (W : PropertyAWitness G R ε) (g h : G) {T₁ T₂ : Finset G}
    (h₁g : ∀ x, W.weight g x ≠ 0 → x ∈ T₁) (h₁h : ∀ x, W.weight h x ≠ 0 → x ∈ T₁)
    (h₂g : ∀ x, W.weight g x ≠ 0 → x ∈ T₂)
    (h₂h : ∀ x, W.weight h x ≠ 0 → x ∈ T₂) :
    ∑ x ∈ T₁, |W.weight g x - W.weight h x|
      = ∑ x ∈ T₂, |W.weight g x - W.weight h x| := by
  classical
  have hz₁ : ∀ x : G, x ∉ T₁ → |W.weight g x - W.weight h x| = 0 := by
    intro x hx
    have hg : W.weight g x = 0 := by
      by_contra hc
      exact hx (h₁g x hc)
    have hh : W.weight h x = 0 := by
      by_contra hc
      exact hx (h₁h x hc)
    rw [hg, hh, sub_zero, abs_zero]
  have hz₂ : ∀ x : G, x ∉ T₂ → |W.weight g x - W.weight h x| = 0 := by
    intro x hx
    have hg : W.weight g x = 0 := by
      by_contra hc
      exact hx (h₂g x hc)
    have hh : W.weight h x = 0 := by
      by_contra hc
      exact hx (h₂h x hc)
    rw [hg, hh, sub_zero, abs_zero]
  have e₁ : ∑ x ∈ T₁, |W.weight g x - W.weight h x|
      = ∑ x ∈ T₁ ∪ T₂, |W.weight g x - W.weight h x| :=
    Finset.sum_subset Finset.subset_union_left fun x _ hx ↦ hz₁ x hx
  have e₂ : ∑ x ∈ T₂, |W.weight g x - W.weight h x|
      = ∑ x ∈ T₁ ∪ T₂, |W.weight g x - W.weight h x| :=
    Finset.sum_subset Finset.subset_union_right fun x _ hx ↦ hz₂ x hx
  rw [e₁, e₂]

end PropertyAWitness

/-! ## Link `E.1`: locally finite groups

This is the only one of the four links of the manuscript's chain that is
elementary.  In a locally finite group the finite scale `R` sits inside a
*finite subgroup* `H`, and the uniform measure on the coset `g·H` is
**exactly** invariant under translating the base point inside `H`: if
`g⁻¹h ∈ R ⊆ H` then `gH = hH`, so the two measures coincide and the `ℓ¹`
defect is `0`, for every `ε`.  No Følner estimate and no limit is needed. -/

/-- **A locally finite group has property A.** -/
theorem hasPropertyA_of_isLocallyFiniteGroup {G : Type u} [Group G]
    (hG : IsLocallyFiniteGroup G) : HasPropertyA G := by
  classical
  intro R ε hε
  obtain ⟨H, hHfin, hRH⟩ := hG R
  -- Realize the finite subgroup `H` as a `Finset` of `G`.
  obtain ⟨S, hmemS⟩ : ∃ S : Finset G, ∀ x : G, x ∈ S ↔ x ∈ H := by
    haveI := hHfin
    haveI : Fintype ↥H := Fintype.ofFinite ↥H
    refine ⟨Finset.image (fun y : ↥H ↦ (y : G)) Finset.univ, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hx
      rw [← ha]
      exact a.2
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hone : (1 : G) ∈ S := (hmemS 1).mpr H.one_mem
  have hcardpos : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcardne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcardpos.ne'
  refine ⟨{
    template := S
    weight := fun g x ↦ if g⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0
    weight_nonneg := ?_
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  · intro g x
    show (0 : ℝ) ≤ (if g⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)
    by_cases hx : g⁻¹ * x ∈ S
    · rw [if_pos hx]
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_of_eq (if_neg hx).symm
  · intro g x hx
    exact if_neg hx
  · intro g
    show ∑ s ∈ S, (if g⁻¹ * (g * s) ∈ S then ((S.card : ℝ))⁻¹ else 0) = 1
    have hterm : ∀ s ∈ S,
        (if g⁻¹ * (g * s) ∈ S then ((S.card : ℝ))⁻¹ else 0)
          = ((S.card : ℝ))⁻¹ := by
      intro s hs
      have hmem : g⁻¹ * (g * s) ∈ S := by
        rw [inv_mul_cancel_left]
        exact hs
      exact if_pos hmem
    have hsum : ∑ s ∈ S, (if g⁻¹ * (g * s) ∈ S then ((S.card : ℝ))⁻¹ else 0)
        = ∑ _s ∈ S, ((S.card : ℝ))⁻¹ := Finset.sum_congr rfl hterm
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcardne
  · intro g h hgh T _ _
    show ∑ x ∈ T, |(if g⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)
        - (if h⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)| ≤ ε
    have hHgh : g⁻¹ * h ∈ H := hRH _ hgh
    have hiff : ∀ x : G, (g⁻¹ * x ∈ S) ↔ (h⁻¹ * x ∈ S) := by
      intro x
      have hA : (g⁻¹ * h)⁻¹ * (g⁻¹ * x) = h⁻¹ * x := by
        rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      have hB : (g⁻¹ * h) * (h⁻¹ * x) = g⁻¹ * x := by
        rw [mul_assoc, mul_inv_cancel_left]
      simp only [hmemS]
      refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
      · rw [← hA]
        exact H.mul_mem (H.inv_mem hHgh) hx
      · rw [← hB]
        exact H.mul_mem hHgh hx
    have hzero : ∀ x ∈ T,
        |(if g⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)
          - (if h⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)| = 0 := by
      intro x _
      by_cases hx : g⁻¹ * x ∈ S
      · rw [if_pos hx, if_pos ((hiff x).mp hx), sub_self, abs_zero]
      · rw [if_neg hx, if_neg fun hc ↦ hx ((hiff x).mpr hc), sub_self, abs_zero]
    rw [Finset.sum_eq_zero hzero]
    exact hε.le

/-- **Finite groups have property A**, as the degenerate case of local
finiteness. -/
theorem hasPropertyA_of_finite (G : Type u) [Group G] [Finite G] :
    HasPropertyA G :=
  hasPropertyA_of_isLocallyFiniteGroup (isLocallyFiniteGroup_of_finite G)

open CliffordLamp in
/-! ## Link `E.1` along the manuscript's own route, through amenability

The manuscript does not say "locally finite, hence property A"; it says
*"the locally finite lamp kernel is amenable and hence exact"*.  The
intermediate object is amenability, so this section supplies it and routes
`E.1` through it.

Amenability is taken in **Day's `ℓ¹` form**: finitely supported probability
weights that are almost invariant under translation by a finite scale.  That is
the form amenability has to be in before it can feed property A --- the
invariant-mean form already in this repository
(`GroupApproximation.Amenability.IsAmenable`) cannot, because recovering
almost invariant weights from a mean is Day's theorem, which is not formalized
anywhere here.  Which form is used is therefore recorded explicitly rather than
hidden: `HasAlmostInvariantWeights` is amenability, and `Day's theorem` is the
unformalized bridge to the mean formulation. -/

/-- **Amenability in Day's `ℓ¹` form.**  For every finite scale `R` and every
tolerance `ε` there is a finitely supported probability weight on `G` whose
`ℓ¹` displacement under left translation by any `r ∈ R` is at most `ε`.

As in `PropertyAWitness`, the `ℓ¹` sum is taken over an arbitrary finite `T`
containing the two supports, which avoids a `DecidableEq G` side condition and
is exactly the `ℓ¹` norm of the difference. -/
def HasAlmostInvariantWeights (G : Type u) [Group G] : Prop :=
  ∀ (R : Finset G) (ε : ℝ), 0 < ε → ∃ (F : Finset G) (f : G → ℝ),
    (∀ x, 0 ≤ f x) ∧ (∀ x, x ∉ F → f x = 0) ∧ (∑ x ∈ F, f x = 1) ∧
      ∀ r ∈ R, ∀ T : Finset G, (∀ x, f x ≠ 0 → x ∈ T) →
        (∀ x, f (r⁻¹ * x) ≠ 0 → x ∈ T) → ∑ x ∈ T, |f x - f (r⁻¹ * x)| ≤ ε

/-- **A locally finite group is amenable**, in Day's `ℓ¹` form.  The finite
scale `R` lies in a finite subgroup `H`; the uniform weight on `H` is *exactly*
invariant under translation by elements of `H`, so the displacement is `0`. -/
theorem hasAlmostInvariantWeights_of_isLocallyFiniteGroup {G : Type u} [Group G]
    (hG : IsLocallyFiniteGroup G) : HasAlmostInvariantWeights G := by
  classical
  intro R ε hε
  obtain ⟨H, hHfin, hRH⟩ := hG R
  obtain ⟨S, hmemS⟩ : ∃ S : Finset G, ∀ x : G, x ∈ S ↔ x ∈ H := by
    haveI := hHfin
    haveI : Fintype ↥H := Fintype.ofFinite ↥H
    refine ⟨Finset.image (fun y : ↥H ↦ (y : G)) Finset.univ, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hx
      rw [← ha]
      exact a.2
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hone : (1 : G) ∈ S := (hmemS 1).mpr H.one_mem
  have hcardpos : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcardne : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcardpos.ne'
  refine ⟨S, fun x ↦ if x ∈ S then ((S.card : ℝ))⁻¹ else 0, ?_, ?_, ?_, ?_⟩
  · intro x
    show (0 : ℝ) ≤ (if x ∈ S then ((S.card : ℝ))⁻¹ else 0)
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_of_eq (if_neg hx).symm
  · intro x hx
    exact if_neg hx
  · show ∑ x ∈ S, (if x ∈ S then ((S.card : ℝ))⁻¹ else 0) = 1
    have hterm : ∀ x ∈ S,
        (if x ∈ S then ((S.card : ℝ))⁻¹ else 0) = ((S.card : ℝ))⁻¹ :=
      fun x hx ↦ if_pos hx
    have hsum : ∑ x ∈ S, (if x ∈ S then ((S.card : ℝ))⁻¹ else 0)
        = ∑ _x ∈ S, ((S.card : ℝ))⁻¹ := Finset.sum_congr rfl hterm
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcardne
  · intro r hr T _ _
    show ∑ x ∈ T, |(if x ∈ S then ((S.card : ℝ))⁻¹ else 0)
        - (if r⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)| ≤ ε
    have hrH : r ∈ H := hRH _ hr
    have hiff : ∀ x : G, (x ∈ S) ↔ (r⁻¹ * x ∈ S) := by
      intro x
      simp only [hmemS]
      refine ⟨fun hx ↦ H.mul_mem (H.inv_mem hrH) hx, fun hx ↦ ?_⟩
      have hB : r * (r⁻¹ * x) = x := mul_inv_cancel_left r x
      rw [← hB]
      exact H.mul_mem hrH hx
    have hzero : ∀ x ∈ T,
        |(if x ∈ S then ((S.card : ℝ))⁻¹ else 0)
          - (if r⁻¹ * x ∈ S then ((S.card : ℝ))⁻¹ else 0)| = 0 := by
      intro x _
      by_cases hx : x ∈ S
      · rw [if_pos hx, if_pos ((hiff x).mp hx), sub_self, abs_zero]
      · rw [if_neg hx, if_neg fun hc ↦ hx ((hiff x).mpr hc), sub_self, abs_zero]
    rw [Finset.sum_eq_zero hzero]
    exact hε.le

/-- **Amenability implies property A**, in the quantitative forms of both.

The property-A measure attached to the base point `g` is the almost invariant
weight translated to `g`.  The `ℓ¹` estimate is the almost invariance of the
weight, read in the coordinates `y = g⁻¹x`, in which `h⁻¹x` becomes
`(g⁻¹h)⁻¹y`; the reindexing is the bijection `x ↦ g⁻¹x`.

Together with `hasAlmostInvariantWeights_of_isLocallyFiniteGroup` this is the
manuscript's `E.1` with its own intermediate object in place. -/
theorem hasPropertyA_of_hasAlmostInvariantWeights {G : Type u} [Group G]
    (hG : HasAlmostInvariantWeights G) : HasPropertyA G := by
  classical
  intro R ε hε
  obtain ⟨F, f, hnonneg, hsupp, hmass, hinv⟩ := hG R ε hε
  refine ⟨{
    template := F
    weight := fun g x ↦ f (g⁻¹ * x)
    weight_nonneg := ?_
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  · intro g x
    exact hnonneg _
  · intro g x hx
    exact hsupp _ hx
  · intro g
    show ∑ s ∈ F, f (g⁻¹ * (g * s)) = 1
    have hterm : ∀ s ∈ F, f (g⁻¹ * (g * s)) = f s := by
      intro s _
      rw [inv_mul_cancel_left]
    have hsum : ∑ s ∈ F, f (g⁻¹ * (g * s)) = ∑ s ∈ F, f s :=
      Finset.sum_congr rfl hterm
    rw [hsum]
    exact hmass
  · intro g h hgh T hTg hTh
    show ∑ x ∈ T, |f (g⁻¹ * x) - f (h⁻¹ * x)| ≤ ε
    have hA : ∀ x : G, (g⁻¹ * h)⁻¹ * (g⁻¹ * x) = h⁻¹ * x := by
      intro x
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    have hinj : Set.InjOn (fun x : G ↦ g⁻¹ * x) (T : Set G) := by
      intro a _ b _ hab
      exact mul_left_cancel hab
    have hwin1 : ∀ y : G, f y ≠ 0 → y ∈ T.image (fun x : G ↦ g⁻¹ * x) := by
      intro y hy
      have hgy : g * y ∈ T := by
        refine hTg (g * y) ?_
        show f (g⁻¹ * (g * y)) ≠ 0
        rwa [inv_mul_cancel_left]
      exact Finset.mem_image.mpr ⟨g * y, hgy, inv_mul_cancel_left g y⟩
    have hwin2 : ∀ y : G, f ((g⁻¹ * h)⁻¹ * y) ≠ 0 →
        y ∈ T.image (fun x : G ↦ g⁻¹ * x) := by
      intro y hy
      have hgy : g * y ∈ T := by
        refine hTh (g * y) ?_
        show f (h⁻¹ * (g * y)) ≠ 0
        rw [← hA (g * y), inv_mul_cancel_left]
        exact hy
      exact Finset.mem_image.mpr ⟨g * y, hgy, inv_mul_cancel_left g y⟩
    have hday : ∑ y ∈ T.image (fun x : G ↦ g⁻¹ * x),
        |f y - f ((g⁻¹ * h)⁻¹ * y)| ≤ ε :=
      hinv (g⁻¹ * h) hgh (T.image (fun x : G ↦ g⁻¹ * x)) hwin1 hwin2
    have hreindex : ∑ y ∈ T.image (fun x : G ↦ g⁻¹ * x),
          |f y - f ((g⁻¹ * h)⁻¹ * y)|
        = ∑ x ∈ T, |f (g⁻¹ * x) - f ((g⁻¹ * h)⁻¹ * (g⁻¹ * x))| :=
      Finset.sum_image hinj
    have hEq : ∑ x ∈ T, |f (g⁻¹ * x) - f ((g⁻¹ * h)⁻¹ * (g⁻¹ * x))|
        = ∑ x ∈ T, |f (g⁻¹ * x) - f (h⁻¹ * x)| := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [hA x]
    calc ∑ x ∈ T, |f (g⁻¹ * x) - f (h⁻¹ * x)|
        = ∑ x ∈ T, |f (g⁻¹ * x) - f ((g⁻¹ * h)⁻¹ * (g⁻¹ * x))| := hEq.symm
      _ = ∑ y ∈ T.image (fun x : G ↦ g⁻¹ * x),
            |f y - f ((g⁻¹ * h)⁻¹ * y)| := hreindex.symm
      _ ≤ ε := hday

/-- **Link `E.1`, along the manuscript's route.**  Locally finite `⟹` amenable
`⟹` property A.  Same conclusion as `hasPropertyA_of_isLocallyFiniteGroup`,
but with the manuscript's intermediate object present rather than bypassed. -/
theorem hasPropertyA_of_isLocallyFiniteGroup_viaAmenability {G : Type u}
    [Group G] (hG : IsLocallyFiniteGroup G) : HasPropertyA G :=
  hasPropertyA_of_hasAlmostInvariantWeights
    (hasAlmostInvariantWeights_of_isLocallyFiniteGroup hG)

open CliffordLamp in
/-- **The lamp kernel, along the manuscript's route.**  `ClLamp(X)` is locally
finite, hence amenable, hence has property A. -/
theorem hasPropertyA_cliffordLamp_viaAmenability (X : Type u) :
    HasPropertyA (CliffordLamp X) :=
  hasPropertyA_of_isLocallyFiniteGroup_viaAmenability
    (isLocallyFiniteGroup_cliffordLamp X)

end ExactnessPermanence
end GroupApproximation
