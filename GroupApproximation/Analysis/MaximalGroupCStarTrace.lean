import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful

/-!
# The canonical trace on the maximal group C-star algebra

`Analysis.MaximalGroupCStar` builds the universe-relative maximal group
C-star algebra together with the evaluation map at any same-universe unitary
representation.  Evaluating at the concrete left regular representation gives
the canonical map

`q : C*(G) → C*_r(G)`,

and `Analysis.ReducedGroupCStarTraceFaithful` supplies the canonical faithful
trace `τ_r` on the target.  This file composes them into the canonical trace

`τ_G = τ_r ∘ q : C*(G) → ℂ`

and proves the single structural fact the rest of the development consumes,

`τ_G (u_g) = if g = 1 then 1 else 0`,

together with the tracial-state properties of `τ_G`: it is normalized,
positive on elements `a⋆ a`, hermitian, and invariant under swapping the
factors of a product.  Finally, the separability argument already used for the
reduced algebra is adapted to the maximal algebra, which needs only that its
generating set is countable.

Faithfulness is deliberately *not* claimed: `q` has a kernel unless `G` is
amenable, and that is exactly why `τ_G` is interesting.
-/

open scoped CStarAlgebra ComplexOrder ENNReal InnerProductSpace Pointwise

namespace GroupApproximation

noncomputable section

universe u

namespace ReducedGroupCStarTrace

variable (G : Type u) [Group G]

/-- The point-mass lemmas quantify over a decidable equality on the group.
This is the same classical instance that `Analysis.ReducedGroupCStarTrace` and
its neighbours install, so the instance argument buried inside `lp.single`
matches theirs syntactically and the point-mass rewrites fire. -/
local instance canonicalMaximalTraceDecidableEq : DecidableEq G :=
  Classical.decEq G

/-- The canonical reduced coefficient is normalized. -/
theorem canonicalCoefficientAtOne_one :
    canonicalCoefficientAtOne G (1 : ReducedGroupCStar G) = 1 := by
  change ((1 : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = 1
  simp [deltaOne]

/-- The canonical reduced coefficient is the matrix coefficient of the
identity vector. -/
theorem canonicalCoefficientAtOne_eq_inner (T : ReducedGroupCStar G) :
    canonicalCoefficientAtOne G T =
      ⟪deltaOne G,
        (T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)⟫_ℂ := by
  change ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = _
  rw [deltaOne, lp.inner_single_left]
  simp

/-- The canonical reduced coefficient is hermitian. -/
theorem canonicalCoefficientAtOne_star (T : ReducedGroupCStar G) :
    canonicalCoefficientAtOne G (star T) =
      starRingEnd ℂ (canonicalCoefficientAtOne G T) := by
  rw [canonicalCoefficientAtOne_eq_inner G (star T),
    canonicalCoefficientAtOne_eq_inner G T]
  change ⟪deltaOne G,
    (star (T : GroupHilbert G →L[ℂ] GroupHilbert G)) (deltaOne G)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- The canonical reduced coefficient vanishes on every nonidentity left
regular unitary: its identity column is the point mass at `g`. -/
theorem canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one {g : G}
    (hg : g ≠ 1) : canonicalCoefficientAtOne G (reducedLeftRegular G g) = 0 := by
  change ((reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G)
    (deltaOne G)) 1 = 0
  rw [reducedLeftRegular_deltaOne, lp.coeFn_single,
    Pi.single_eq_of_ne (Ne.symm hg)]

end ReducedGroupCStarTrace

open ReducedGroupCStarTrace

variable (G : Type u) [Group G]

/-- The canonical map from the maximal group C-star algebra to the concrete
reduced group C-star algebra: evaluation of the universal diagonal
representation at the left regular coordinate. -/
def maximalGroupCStarToReduced :
    MaximalGroupCStar G →⋆ₐ[ℂ] ReducedGroupCStar G :=
  maximalGroupCStarEval G (CStarUnitaryRepresentation.reduced G)

@[simp] theorem maximalGroupCStarToReduced_generator (g : G) :
    maximalGroupCStarToReduced G (maximalGroupCStarGenerator G g) =
      reducedLeftRegular G g :=
  rfl

/-- The canonical trace on the maximal group C-star algebra: the canonical
faithful trace of the reduced algebra, pulled back along the canonical map. -/
def canonicalMaximalTrace : MaximalGroupCStar G →L[ℂ] ℂ where
  toFun a := canonicalCoefficientAtOne G (maximalGroupCStarToReduced G a)
  map_add' a b := by simp
  map_smul' c a := by simp
  cont := (canonicalCoefficientAtOne G).continuous.comp
    (map_continuous (maximalGroupCStarToReduced G))

/-- The defining factorization `τ_G = τ_r ∘ q`. -/
@[simp] theorem canonicalMaximalTrace_apply (a : MaximalGroupCStar G) :
    canonicalMaximalTrace G a =
      canonicalCoefficientAtOne G (maximalGroupCStarToReduced G a) :=
  rfl

/-- The canonical trace is normalized. -/
theorem canonicalMaximalTrace_one : canonicalMaximalTrace G 1 = 1 := by
  rw [canonicalMaximalTrace_apply, map_one, canonicalCoefficientAtOne_one]

/-- The canonical trace of the identity generator. -/
theorem canonicalMaximalTrace_generator_one :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G 1) = 1 := by
  rw [canonicalMaximalTrace_apply, maximalGroupCStarToReduced_generator,
    reducedLeftRegular_one, canonicalCoefficientAtOne_one]

/-- The canonical trace kills every nonidentity generator. -/
theorem canonicalMaximalTrace_generator_of_ne_one {g : G} (hg : g ≠ 1) :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G g) = 0 := by
  rw [canonicalMaximalTrace_apply, maximalGroupCStarToReduced_generator,
    canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one G hg]

/-- **The generator formula.**  The canonical trace of the canonical generator
`u_g` is `1` at the identity and `0` everywhere else. -/
theorem canonicalMaximalTrace_generator (g : G) [Decidable (g = 1)] :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G g) =
      if g = 1 then 1 else 0 := by
  by_cases hg : g = 1
  · rw [if_pos hg, hg]
    exact canonicalMaximalTrace_generator_one G
  · rw [if_neg hg]
    exact canonicalMaximalTrace_generator_of_ne_one G hg

/-- The generator formula, stated for the canonical unitary representation of
the group inside its maximal C-star algebra. -/
theorem canonicalMaximalTrace_unitaryHom (g : G) [Decidable (g = 1)] :
    canonicalMaximalTrace G
        ((maximalGroupCStarUnitaryHom G g : unitary (MaximalGroupCStar G)) :
          MaximalGroupCStar G) =
      if g = 1 then 1 else 0 :=
  canonicalMaximalTrace_generator G g

/-- The canonical trace is positive. -/
theorem canonicalMaximalTrace_star_mul_self_nonneg (a : MaximalGroupCStar G) :
    0 ≤ canonicalMaximalTrace G (star a * a) := by
  rw [canonicalMaximalTrace_apply, map_mul, map_star,
    canonicalCoefficientAtOne_star_mul_self]
  positivity

/-- The canonical trace is hermitian. -/
theorem canonicalMaximalTrace_star (a : MaximalGroupCStar G) :
    canonicalMaximalTrace G (star a) =
      starRingEnd ℂ (canonicalMaximalTrace G a) := by
  rw [canonicalMaximalTrace_apply, canonicalMaximalTrace_apply, map_star,
    canonicalCoefficientAtOne_star]

/-- The canonical trace is tracial. -/
theorem canonicalMaximalTrace_mul_comm (a b : MaximalGroupCStar G) :
    canonicalMaximalTrace G (a * b) = canonicalMaximalTrace G (b * a) := by
  rw [canonicalMaximalTrace_apply, canonicalMaximalTrace_apply,
    map_mul (maximalGroupCStarToReduced G) a b,
    map_mul (maximalGroupCStarToReduced G) b a,
    canonicalCoefficientAtOne_mul_comm G (maximalGroupCStarToReduced G a)
      (maximalGroupCStarToReduced G b)]

/-- **The canonical trace is a tracial state**: normalized, positive, and
invariant under swapping the factors of a product. -/
theorem canonicalMaximalTrace_isTracialState :
    canonicalMaximalTrace G 1 = 1 ∧
      (∀ a : MaximalGroupCStar G, 0 ≤ canonicalMaximalTrace G (star a * a)) ∧
      (∀ a b : MaximalGroupCStar G,
        canonicalMaximalTrace G (a * b) = canonicalMaximalTrace G (b * a)) :=
  ⟨canonicalMaximalTrace_one G, canonicalMaximalTrace_star_mul_self_nonneg G,
    canonicalMaximalTrace_mul_comm G⟩

/-! ## Density of the canonical generators

The canonical generators are not merely a generating set: they are a group of
unitaries, closed under multiplication and star and containing `1`.  So the
star algebra they generate is already their *linear span*, and the maximal
algebra — the closure of that star algebra — is the closure of that span.
Two continuous linear maps agreeing on the generators therefore agree
everywhere.  This is what turns the generator formula into a statement about
the whole algebra, and it is the form both consumers of the trace need. -/

/-- The canonical generators of the ambient bounded product, as a monoid map
out of the group. -/
def maximalGroupCStarAmbientHom : G →* MaximalGroupCStarAmbient G :=
  (unitary (MaximalGroupCStarAmbient G)).subtype.comp
    (maximalGroupCStarAmbientRepresentation G)

@[simp] theorem maximalGroupCStarAmbientHom_apply (g : G) :
    maximalGroupCStarAmbientHom G g =
      (maximalGroupCStarGenerator G g : MaximalGroupCStarAmbient G) :=
  rfl

/-- The star of a canonical generator is the generator at the inverse group
element.  Only the unitarity of the generators and multiplicativity of the
representation are used: a two-sided inverse in a monoid is unique. -/
theorem star_maximalGroupCStarAmbientHom (g : G) :
    star (maximalGroupCStarAmbientHom G g) =
      maximalGroupCStarAmbientHom G g⁻¹ := by
  have hsa : maximalGroupCStarAmbientHom G g *
      star (maximalGroupCStarAmbientHom G g) = 1 :=
    (maximalGroupCStarAmbientRepresentation G g).property.2
  have hinv : maximalGroupCStarAmbientHom G g⁻¹ *
      maximalGroupCStarAmbientHom G g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc star (maximalGroupCStarAmbientHom G g)
      = maximalGroupCStarAmbientHom G g⁻¹ * maximalGroupCStarAmbientHom G g *
          star (maximalGroupCStarAmbientHom G g) := by rw [hinv, one_mul]
    _ = maximalGroupCStarAmbientHom G g⁻¹ *
          (maximalGroupCStarAmbientHom G g *
            star (maximalGroupCStarAmbientHom G g)) := by rw [mul_assoc]
    _ = maximalGroupCStarAmbientHom G g⁻¹ := by rw [hsa, mul_one]

/-- The star algebra generated by the canonical generators is contained in
their linear span: the monoid they generate, star included, is the set of
generators itself. -/
theorem maximalGroupCStarAdjoin_le_span :
    (StarAlgebra.adjoin ℂ
        (Set.range ⇑(maximalGroupCStarAmbientHom G))).toSubalgebra.toSubmodule ≤
      Submodule.span ℂ (Set.range ⇑(maximalGroupCStarAmbientHom G)) := by
  rw [StarAlgebra.adjoin_eq_span]
  apply Submodule.span_mono
  have hle : Submonoid.closure
      (Set.range ⇑(maximalGroupCStarAmbientHom G) ∪
        star (Set.range ⇑(maximalGroupCStarAmbientHom G))) ≤
      MonoidHom.mrange (maximalGroupCStarAmbientHom G) := by
    apply Submonoid.closure_le.mpr
    rintro x (⟨g, rfl⟩ | hx)
    · exact ⟨g, rfl⟩
    · rw [← Set.image_star] at hx
      obtain ⟨y, ⟨g, rfl⟩, rfl⟩ := hx
      exact ⟨g⁻¹, (star_maximalGroupCStarAmbientHom G g).symm⟩
  intro x hx
  exact hle hx

/-- **The span of the canonical generators is dense.** -/
theorem maximalGroupCStar_dense_span_generator :
    Dense (Submodule.span ℂ (Set.range (maximalGroupCStarGenerator G)) :
      Set (MaximalGroupCStar G)) := by
  have himg : ∀ y ∈ Submodule.span ℂ
      (Set.range ⇑(maximalGroupCStarAmbientHom G)),
      y ∈ Subtype.val ''
        (Submodule.span ℂ (Set.range (maximalGroupCStarGenerator G)) :
          Set (MaximalGroupCStar G)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨maximalGroupCStarGenerator G g,
          Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, Submodule.add_mem _ ha hb, rfl⟩
    | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨c • a, Submodule.smul_mem _ c ha, rfl⟩
  refine (Subtype.dense_iff (s := (maximalGroupCStarSubalgebra G :
    Set (MaximalGroupCStarAmbient G)))).mpr ?_
  intro y hy
  have hy' : y ∈ closure ((StarAlgebra.adjoin ℂ
      (Set.range ⇑(maximalGroupCStarAmbientHom G)) :
        StarSubalgebra ℂ (MaximalGroupCStarAmbient G)) :
      Set (MaximalGroupCStarAmbient G)) := by
    rw [← StarSubalgebra.topologicalClosure_coe]
    exact hy
  refine closure_mono ?_ hy'
  intro z hz
  exact himg z (maximalGroupCStarAdjoin_le_span G hz)

/-- **Uniqueness from the generators.**  Two continuous linear maps out of the
maximal group C-star algebra that agree on every canonical generator are
equal. -/
theorem maximalGroupCStar_ext_of_generator {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {f h : MaximalGroupCStar G →L[ℂ] F}
    (hfh : ∀ g : G,
      f (maximalGroupCStarGenerator G g) = h (maximalGroupCStarGenerator G g)) :
    f = h :=
  ContinuousLinearMap.ext_on (maximalGroupCStar_dense_span_generator G)
    (by
      rintro _ ⟨g, rfl⟩
      exact hfh g)

/-- The scalar case, which is the one both consumers use: a continuous linear
functional on the maximal algebra is determined by its values on the canonical
unitaries. -/
theorem maximalGroupCStar_ext_of_generator_functional
    {f h : MaximalGroupCStar G →L[ℂ] ℂ}
    (hfh : ∀ g : G,
      f (maximalGroupCStarGenerator G g) = h (maximalGroupCStarGenerator G g)) :
    f = h :=
  maximalGroupCStar_ext_of_generator G hfh

/-- **The canonical trace is the only continuous linear functional with the
canonical generator values.**  A trace obtained some other way — from a
representation into a tracial ultraproduct, say — is `τ_G` as soon as it takes
the value `1` at the identity generator and `0` at the others. -/
theorem canonicalMaximalTrace_eq_of_generator
    (f : MaximalGroupCStar G →L[ℂ] ℂ)
    (h1 : f (maximalGroupCStarGenerator G 1) = 1)
    (hne : ∀ g : G, g ≠ 1 → f (maximalGroupCStarGenerator G g) = 0) :
    f = canonicalMaximalTrace G := by
  refine maximalGroupCStar_ext_of_generator_functional G ?_
  intro g
  by_cases hg : g = 1
  · rw [hg, h1, canonicalMaximalTrace_generator_one]
  · rw [hne g hg, canonicalMaximalTrace_generator_of_ne_one G hg]

/-! ## Factoring the canonical trace through a unitary model

This is the step the hyperlinear half of the trace program consumes.  Given
*any* unital C-star algebra `B` carrying a group of unitaries indexed by `G`
and a continuous normalized functional that vanishes on the nonidentity
unitaries, the canonical trace of `C*(G)` factors through `B`: the universal
property of the *full* group C-star algebra extends the unitary
representation to `π : C*(G) → B`, and `τ_B ∘ π` agrees with `τ_G` on the
generators, hence — by `maximalGroupCStar_ext_of_generator` — everywhere.

The intended `B` is the tracial matrix ultraproduct `Mω` of a sofic
approximation, where `τ_B` is the ultratrace.  Nothing here depends on that
choice, and nothing here is about soficity: the sofic input is exactly the
construction of `rho` together with the vanishing hypothesis `hne`, and it is
deliberately not assumed in disguise.

Note which hypothesis is *not* needed.  The value at the identity is not an
asymptotic statement about traces of approximating matrices: `rho` is a monoid
homomorphism, so `rho 1 = 1` on the nose, and normalization of `τ_B` does the
rest.  A sofic approximation only satisfies `σₙ(1) ≈ 1`, so asking for the
identity value as a limit would have been both harder and unnecessary. -/

/-- A ⋆-homomorphism out of the maximal algebra, followed by a continuous
functional on the target, packaged as a continuous functional.  A ⋆-morphism
between C-star algebras is automatically contractive, which is where the
continuity comes from. -/
def compContinuousFunctional {B : Type u} [CStarAlgebra B]
    (π : MaximalGroupCStar G →⋆ₐ[ℂ] B) (τB : B →L[ℂ] ℂ) :
    MaximalGroupCStar G →L[ℂ] ℂ where
  toFun a := τB (π a)
  map_add' a b := by simp
  map_smul' c a := by simp
  cont := τB.continuous.comp (map_continuous π)

@[simp] theorem compContinuousFunctional_apply {B : Type u} [CStarAlgebra B]
    (π : MaximalGroupCStar G →⋆ₐ[ℂ] B) (τB : B →L[ℂ] ℂ)
    (a : MaximalGroupCStar G) :
    compContinuousFunctional G π τB a = τB (π a) :=
  rfl

/-- **The canonical trace factors through any unitary model with the canonical
trace values.**  If `B` is a unital C-star algebra, `rho : G →* unitary B`,
and `τ_B` is a continuous linear functional with `τ_B 1 = 1` that vanishes on
`rho g` for every `g ≠ 1`, then the universal property supplies
`π : C*(G) →⋆ₐ[ℂ] B` with `π (u_g) = rho g`, and `τ_B ∘ π` is *equal* to the
canonical trace — not merely equal on the generators.

Instantiated at a tracial matrix ultraproduct of a sofic approximation, this
is "the canonical trace of a sofic group factors through `Mω`", which is the
hyperlinear half of the trace separation. -/
theorem canonicalMaximalTrace_factorsThrough {B : Type u} [CStarAlgebra B]
    (rho : G →* unitary B) (τB : B →L[ℂ] ℂ)
    (hone : τB (1 : B) = 1)
    (hne : ∀ g : G, g ≠ 1 → τB ((rho g : unitary B) : B) = 0) :
    ∃ π : MaximalGroupCStar G →⋆ₐ[ℂ] B,
      (∀ g : G,
        π (maximalGroupCStarGenerator G g) = ((rho g : unitary B) : B)) ∧
        compContinuousFunctional G π τB = canonicalMaximalTrace G := by
  obtain ⟨π, hπ, -⟩ := maximalGroupCStar_existsUnique_lift G rho
  refine ⟨π, hπ, ?_⟩
  refine canonicalMaximalTrace_eq_of_generator G _ ?_ ?_
  · have hrho : ((rho (1 : G) : unitary B) : B) = 1 :=
      congrArg (fun U : unitary B ↦ (U : B)) (map_one rho)
    show τB (π (maximalGroupCStarGenerator G 1)) = 1
    rw [hπ 1, hrho]
    exact hone
  · intro g hg
    show τB (π (maximalGroupCStarGenerator G g)) = 0
    rw [hπ g]
    exact hne g hg

/-- The maximal group C-star algebra of a countable group is separable: it is
the norm closure of the star algebra generated by the countable set of
canonical generators.  The ambient bounded product is *not* separable, so the
argument is the one already used for the reduced algebra. -/
theorem maximalGroupCStar_separableSpace [Countable G] :
    TopologicalSpace.SeparableSpace (MaximalGroupCStar G) := by
  let A := MaximalGroupCStarAmbient G
  let s : Set A := Set.range (fun g : G ↦
    (maximalGroupCStarAmbientRepresentation G g : MaximalGroupCStarAmbient G))
  have hs : s.Countable := Set.countable_range _
  have hsStar : (star s : Set A).Countable := by
    rw [← Set.image_star]
    exact hs.image _
  let t : Set A := s ∪ star s
  have ht : t.Countable := by
    simpa [t] using hs.union hsStar
  letI : Countable ↥t := ht.to_subtype
  have hmonoid :
      ((Submonoid.closure t : Submonoid A) : Set A).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  have hadjoin :
      TopologicalSpace.IsSeparable
        ((StarAlgebra.adjoin ℂ s : StarSubalgebra ℂ A) : Set A) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
    rw [StarAlgebra.adjoin_eq_span]
    simpa [t] using hmonoid.isSeparable.span
  have hclosed : TopologicalSpace.IsSeparable
      ((maximalGroupCStarSubalgebra G : StarSubalgebra ℂ A) : Set A) := by
    change TopologicalSpace.IsSeparable
      (((StarAlgebra.adjoin ℂ s).topologicalClosure :
        StarSubalgebra ℂ A) : Set A)
    rw [StarSubalgebra.topologicalClosure_coe]
    exact hadjoin.closure
  exact hclosed.separableSpace

end

end GroupApproximation
