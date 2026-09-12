import GroupApproximation.CharClass.RelativeProdContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# Homotopy invariance of relative pullbacks, when the source pair is a line

Lane `lix-hsq`.

Relative cohomology of this development has no chain-level homotopy operator: the
prism construction was never ported, and `RelativeHomotopyInvariance.lean` gives
only the five lemma, which produces **bijectivity** and not an **equality** of two
pullbacks.  Comparing the two routes of `hsq` needs the equality: the two maps of
pairs it compares differ by a contraction of the base, and nothing makes them
equal on the nose.

**Over `F₂` the equality is free once the source pair is one dimensional**, and
that is what this file records.  `Hom(L, L')` between two `F₂`-lines has exactly
two elements, so two injective maps into a line are the same map; and the two
endpoint slices `x ↦ (b, x)` and `x ↦ (b', x)` of a contractible parameter space
both induce bijections by `RelativeProdContractible.relPullback_slice_bijective`.
So they induce the *same* map, and any homotopy through maps of pairs may be cut
at either end.

Nothing here is special to the LIX objects, and nothing here is special to the
degree: the only hypotheses are that the parameter space is contractible, that
the degree is positive (the five lemma has no term to the left of `H^0`), and
that the source pair's relative group is a line.

**What this does not give.**  It is not homotopy invariance.  If the source
pair's relative group has rank two or more, two homotopic maps of pairs can still
have different pullbacks as far as this file knows, and the mod-2 coefficients are
load-bearing: over any other field two isomorphisms between two lines differ by a
scalar, and the scalar survives.

## Main results

* `RelativeSupport.eq_of_injective_of_line` — two injective linear maps into an
  `F₂`-line agree.
* `RelativeSupport.relPullback_slice_eq_of_line` — the two endpoint slices of a
  contractible parameter induce the same relative pullback.
* `RelativeSupport.relPullback_eq_of_homotopy_of_line` — **the cut**: a homotopy
  through maps of pairs has equal pullbacks at its two ends.
* `RelativeSupport.relPullback_eq_id_of_line` — a self-pullback of a line that is
  injective is the identity.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

/-! ## 1. Two injective maps into a line agree -/

/-- **Two injective `F₂`-linear maps into a line are equal.**  A line has exactly two
elements, so an injective map is determined by where it does *not* send things: the
nonzero values of `f` and of `g` are both the unique nonzero element. -/
theorem eq_of_injective_of_line {A B : Type} [AddCommGroup A] [Module (ZMod 2) A]
    [AddCommGroup B] [Module (ZMod 2) B] (e : B ≃ₗ[ZMod 2] ZMod 2)
    {f g : A →ₗ[ZMod 2] B} (hf : Function.Injective f) (hg : Function.Injective g) :
    f = g := by
  refine LinearMap.ext fun a => ?_
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  · have hfa : f a ≠ 0 := fun h => ha (hf (h.trans (map_zero f).symm))
    have hga : g a ≠ 0 := fun h => ha (hg (h.trans (map_zero g).symm))
    have h1 : e (f a) ≠ 0 := fun h => hfa (e.injective (h.trans (map_zero e).symm))
    have h2 : e (g a) ≠ 0 := fun h => hga (e.injective (h.trans (map_zero e).symm))
    have key : ∀ x y : ZMod 2, x ≠ 0 → y ≠ 0 → x = y := by decide
    exact e.injective (key _ _ h1 h2)

/-- The same, for morphisms of `ModuleCat`. -/
theorem hom_eq_of_injective_of_line {M N : ModuleCat.{0} (ZMod 2)}
    (e : ↥N ≃ₗ[ZMod 2] ZMod 2) {f g : M ⟶ N}
    (hf : Function.Injective f.hom) (hg : Function.Injective g.hom) : f = g :=
  ModuleCat.hom_ext (eq_of_injective_of_line e hf hg)

/-- A self-map of a line that is injective **is** the identity. -/
theorem relPullback_eq_id_of_line {X : TopCat.{0}} {A : Set X} (f : X ⟶ X)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A) (n : ℕ)
    (e : ↥(relCohomology (ZMod 2) X A n) ≃ₗ[ZMod 2] ZMod 2)
    (hinj : Function.Injective (relPullback (ZMod 2) f hf n).hom) :
    relPullback (ZMod 2) f hf n = 𝟙 (relCohomology (ZMod 2) X A n) :=
  hom_eq_of_injective_of_line e hinj (fun _ _ hab => hab)

/-! ## 2. The two endpoint slices of a contractible parameter -/

variable {B E : Type} [TopologicalSpace B] [TopologicalSpace E]

/-- **The two endpoint slices induce the same relative pullback.**  Each is bijective by
the five lemma over the pair sequence (`relPullback_slice_bijective`), and two injective
maps into a line agree. -/
theorem relPullback_slice_eq_of_line (hB : ContractibleSpace B) (b b' : B) (S : Set E)
    (n : ℕ) (hn : 1 ≤ n)
    (e : ↥(relCohomology (ZMod 2) (TopCat.of E) S n) ≃ₗ[ZMod 2] ZMod 2) :
    relPullback (ZMod 2) (sliceMap b E) (slice_mapsTo b S) n
      = relPullback (ZMod 2) (sliceMap b' E) (slice_mapsTo b' S) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hom_eq_of_injective_of_line e (relPullback_slice_bijective hB b S m).1
    (relPullback_slice_bijective hB b' S m).1

/-! ## 3. Cutting a homotopy at either end -/

/-- **A homotopy through maps of pairs may be cut at either end**, provided the source
pair's relative group is a line.

`H` is the homotopy, as a single continuous map out of `B × X` with `B` the contractible
parameter space; `hH` is the map-of-pairs condition, which must hold at **every** parameter
and is exactly what makes the two ends comparable.  `hbf` and `hbg` name the two ends. -/
theorem relPullback_eq_of_homotopy_of_line {X : Type} [TopologicalSpace X] {A : Set X}
    {Y : TopCat.{0}} {S : Set Y} (hB : ContractibleSpace B) (b b' : B)
    (H : TopCat.of (B × X) ⟶ Y)
    (hH : ∀ q ∈ {q : B × X | q.2 ∈ A}, (ConcreteCategory.hom H) q ∈ S)
    {f g : TopCat.of X ⟶ Y}
    (hbf : sliceMap b X ≫ H = f) (hbg : sliceMap b' X ≫ H = g)
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ S)
    (hg : ∀ x ∈ A, (ConcreteCategory.hom g) x ∈ S)
    (n : ℕ) (hn : 1 ≤ n)
    (e : ↥(relCohomology (ZMod 2) (TopCat.of X) A n) ≃ₗ[ZMod 2] ZMod 2) :
    relPullback (ZMod 2) f hf n = relPullback (ZMod 2) g hg n := by
  have hcf : ∀ x ∈ A, (ConcreteCategory.hom (sliceMap b X ≫ H)) x ∈ S := fun x hx => hH (b, x) hx
  have hcg : ∀ x ∈ A, (ConcreteCategory.hom (sliceMap b' X ≫ H)) x ∈ S :=
    fun x hx => hH (b', x) hx
  have e1 : relPullback (ZMod 2) (sliceMap b X ≫ H) hcf n = relPullback (ZMod 2) f hf n :=
    relPullback_eq_of_eq (ZMod 2) hbf hcf n
  have e2 : relPullback (ZMod 2) (sliceMap b' X ≫ H) hcg n = relPullback (ZMod 2) g hg n :=
    relPullback_eq_of_eq (ZMod 2) hbg hcg n
  calc relPullback (ZMod 2) f hf n
      = relPullback (ZMod 2) (sliceMap b X ≫ H) hcf n := e1.symm
    _ = relPullback (ZMod 2) H hH n
          ≫ relPullback (ZMod 2) (sliceMap b X) (slice_mapsTo b A) n :=
        relPullback_comp (ZMod 2) (sliceMap b X) H (slice_mapsTo b A) hH hcf n
    _ = relPullback (ZMod 2) H hH n
          ≫ relPullback (ZMod 2) (sliceMap b' X) (slice_mapsTo b' A) n := by
        rw [relPullback_slice_eq_of_line hB b b' A n hn e]
    _ = relPullback (ZMod 2) (sliceMap b' X ≫ H) hcg n :=
        (relPullback_comp (ZMod 2) (sliceMap b' X) H (slice_mapsTo b' A) hH hcg n).symm
    _ = relPullback (ZMod 2) g hg n := e2

end

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the
build** if it leaves the classical allowlist, which `#print axioms` does not. -/

#audit_axioms RelativeSupport.relPullback_eq_of_homotopy_of_line

end RelativeSupport

end GroupApproximation.CharClass
