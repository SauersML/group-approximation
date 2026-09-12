import GroupApproximation.CharClass.OddPTupleSign
import GroupApproximation.CharClass.OddPSingular

/-!
# `∂ ∘ ∂ = 0` for a single slot, for free

The square-zero law of the tuple differential splits into three groups: the two
mixed terms, which cancel by the prefix asymmetry of `OddPTupleSign.lean`, and
the diagonal terms, which need `∂ ∘ ∂ = 0` **within one slot**.

That third group is the expensive one if taken literally: proving it from the
simplicial identity `d_i d_j = d_{j-1} d_i` is a pairing argument over
`Fin (n+2) × Fin (n+3)` with `Fin.pred`/`Fin.castPred` side conditions, and it is
exactly what `CartanSingular.lean`'s module docstring says routing through
`alternatingFaceMapComplex` exists to avoid.

So this file does not take it literally.  `tagBd` is the explicit alternating
face sum, which is what the sign computation needs; `singFreeR`'s differential is
the same thing packaged as a `HomologicalComplex`, which is what `d_comp_d`
applies to.  `tagBd_eq` identifies them, and `tagBdL_tagBdL` is then Mathlib's
`d_comp_d` plus the bookkeeping of re-tagging a simplex with its own degree.

The same move paid for `OddPSingular.lean`: keep the explicit formula where the
signs are needed and borrow the structural law from the categorical packaging.

## STATUS: PARKED AND RED (2026-09-10).  Imported by nothing.

Two errors, both bookkeeping, neither mathematical, after four probe rounds:

* the parity branch of `tagBd_eq` reports `typeclass instance problem is stuck`
  on a `Module` whose four arguments are metavariables.  Naming the ring in the
  `neg_one_pow` steps did not clear it, so the stuck instance is most likely in
  the `one_smul`/`one_zsmul` step, not in the sign lemma.
* the degree-`n+2` branch's final rewrite does not match, after both the
  all-arguments-explicit form and cc-cartan's `let F := …` ascription.  The
  `ModuleCat` carrier and the raw `Finsupp` are definitionally equal and not
  syntactically equal, and I have not found the spelling that fires.

**Do not "fix" this by proving `∂∂ = 0` from the simplicial identity instead.**
I checked: that identity is *not* in the vendored layer under any spelling, so
the "direct" route means proving it over a product of two `Fin` index types with
the predecessor and cast side conditions — which is the argument the mod-2 lane
built its categorical route to avoid, and is larger than this file, not smaller.

**The route that removes this file entirely**: define `tagBd` categorically in
`OddPTuple.lean`, as the differential of `singFreeR` retagged, instead of as an
explicit alternating sum that must then be identified with it.  Degree-drop and
square-zero are then true by construction and there is nothing to bridge.  The
import graph permits it with no cycle, and it does not disturb `OddPTupleSign`,
whose lemmas mention only the prefix sum and the update.

**What the mixed-term cancellation actually needs of the slot boundary** — worth
recording because it is what makes that redefinition free: only that it lowers
degree by exactly one, and that it squares to zero.  Its internal face signs
never enter, because whatever it does inside a slot it does identically in both
orders of differentiation.

**Method note for whoever resumes**: read the full goal at the first error
before touching anything.  Two of this file's four rounds were spent inferring
goals from error text, and both inferences were wrong.  That is the entire
explanation for the four rounds.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- Tag every simplex of a chain with the degree `n`. -/
def tagAt (n : ℕ) : (singularSimplices X n →₀ K) →ₗ[K] (TagSimp X →₀ K) :=
  Finsupp.lmapDomain K K (fun σ => (⟨n, σ⟩ : TagSimp X))

@[simp] theorem tagAt_single (n : ℕ) (σ : singularSimplices X n) :
    tagAt K X n (Finsupp.single σ (1 : K)) = Finsupp.single (⟨n, σ⟩ : TagSimp X) (1 : K) := by
  rw [tagAt]
  show Finsupp.lmapDomain K K _ _ = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The explicit alternating face sum **is** the differential of `singFreeR`,
re-tagged.  Left as an identity of `Finsupp`s rather than of morphisms, because
that is the form both consumers want. -/
theorem tagBd_eq (n : ℕ) (σ : singularSimplices X (n + 1)) :
    tagBd K X ⟨n + 1, σ⟩
      = tagAt K X n ((((singFreeR K).obj X).d (n + 1) n).hom (Finsupp.single σ (1 : K))) := by
  rw [singFreeR_d_single, tagBd_succ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Bridging the `ℤ`-action to the `K`-action by a cast leaves the module
  -- implicit and the instance search gets stuck.  A parity split needs no cast
  -- at all: the two actions agree because both signs are `±1`.
  rw [map_zsmul, tagAt_single]
  -- each `neg_one_pow` needs its ring named, or the instance search is stuck on
  -- a `Module` whose arguments are all metavariables
  rcases Nat.even_or_odd (i : ℕ) with hpar | hpar
  · have hK : ((-1 : K) ^ (i : ℕ)) = 1 := hpar.neg_one_pow
    have hZ : ((-1 : ℤ) ^ (i : ℕ)) = 1 := hpar.neg_one_pow
    rw [hK, one_smul, hZ, one_zsmul]
  · have hK : ((-1 : K) ^ (i : ℕ)) = -1 := hpar.neg_one_pow
    have hZ : ((-1 : ℤ) ^ (i : ℕ)) = -1 := hpar.neg_one_pow
    rw [hK, neg_smul, one_smul, hZ, neg_zsmul, one_zsmul]

/-- The boundary of a tagged simplex, extended linearly. -/
def tagBdL : (TagSimp X →₀ K) →ₗ[K] (TagSimp X →₀ K) :=
  Finsupp.linearCombination K (tagBd K X)

@[simp] theorem tagBdL_single (τ : TagSimp X) :
    tagBdL K X (Finsupp.single τ (1 : K)) = tagBd K X τ := by
  rw [tagBdL, Finsupp.linearCombination_single, one_smul]

/-- Differentiating a chain that has been tagged at one degree is the same as
differentiating each of its simplices as a tag.  Both sides are linear in the
chain, so it is checked on singletons. -/
theorem tagBdL_tagAt (n : ℕ) (z : singularSimplices X n →₀ K) :
    tagBdL K X (tagAt K X n z)
      = Finsupp.linearCombination K (fun σ' => tagBd K X (⟨n, σ'⟩ : TagSimp X)) z := by
  refine LinearMap.congr_fun ?_ z
  apply Finsupp.lhom_ext'
  intro σ
  apply LinearMap.ext_ring
  show tagBdL K X (tagAt K X n (Finsupp.single σ (1 : K)))
    = Finsupp.linearCombination K (fun σ' => tagBd K X (⟨n, σ'⟩ : TagSimp X))
        (Finsupp.single σ (1 : K))
  rw [tagAt_single, tagBdL_single, Finsupp.linearCombination_single, one_smul]

/-- **`∂ ∘ ∂ = 0` in a single slot**, from `HomologicalComplex.d_comp_d` rather
than from the simplicial identity. -/
theorem tagBdL_tagBdL (τ : TagSimp X) :
    tagBdL K X (tagBdL K X (Finsupp.single τ (1 : K))) = 0 := by
  obtain ⟨n, σ⟩ := τ
  rw [tagBdL_single]
  match n, σ with
  | 0, _ => rw [tagBd_zero, map_zero]
  | 1, σ =>
      -- every tag produced has degree `0`, where `tagBd` vanishes
      rw [tagBd_eq, tagBdL_tagAt]
      have hfun : (fun σ' : singularSimplices X 0 => tagBd K X (⟨0, σ'⟩ : TagSimp X))
          = fun _ => (0 : TagSimp X →₀ K) := funext fun σ' => tagBd_zero K X σ'
      rw [hfun, linearCombinationR_zero_fun]
  | (n + 2), σ =>
      have hdd : ((((singFreeR K).obj X).d (n + 1) n).hom
          ((((singFreeR K).obj X).d (n + 2) (n + 1)).hom (Finsupp.single σ (1 : K)))) = 0 := by
        have h' := congrArg (fun (g : (((singFreeR K).obj X).X (n + 2))
            ⟶ (((singFreeR K).obj X).X n)) => g.hom (Finsupp.single σ (1 : K)))
          (HomologicalComplex.d_comp_d ((singFreeR K).obj X) (n + 2) (n + 1) n)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] at h'
        exact h'
      rw [tagBd_eq, tagBdL_tagAt]
      -- Bind the composite to a name with its type ASCRIBED at the `Finsupp`
      -- spelling.  Left inline, its middle type is the `ModuleCat` carrier,
      -- which is defeq to the `Finsupp` but not syntactically it, and the
      -- rewrite's pattern then fails to match a goal that visibly contains it.
      -- cc-cartan's `let F := …` idiom, and it is not stylistic.
      let F : (singularSimplices X (n + 1) →₀ K) →ₗ[K] (TagSimp X →₀ K) :=
        (tagAt K X n).comp ((((singFreeR K).obj X).d (n + 1) n).hom)
      have hfun : (fun σ' : singularSimplices X (n + 1) => tagBd K X (⟨n + 1, σ'⟩ : TagSimp X))
          = fun σ' => F (Finsupp.single σ' (1 : K)) := by
        funext σ'
        rw [tagBd_eq]
        rfl
      rw [hfun, linearCombinationR_comp_single F]
      show tagAt K X n ((((singFreeR K).obj X).d (n + 1) n).hom
        ((((singFreeR K).obj X).d (n + 2) (n + 1)).hom (Finsupp.single σ (1 : K)))) = 0
      rw [hdd, map_zero]

end

end GroupApproximation.CharClass
