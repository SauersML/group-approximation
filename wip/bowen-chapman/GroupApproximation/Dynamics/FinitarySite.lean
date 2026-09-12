import GroupApproximation.Dynamics.SurjunctivityResiduallyFinite
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Finitary site structures and finite-fiber quotient coordinates

The site groups and their group instances are external parameters. The
structure records residual finiteness, detection, coherent inclusions,
finite support and pointwise-stabilizer invariance. Its finite quotient
coordinates separate arbitrary finite subsets of the semidirect product.
-/

namespace GroupApproximation.Surjunctivity

universe uN uG uX uA uQ uB

variable {N : Type uN} {G : Type uG} {X : Type uX}
  [Group N] [Group G] [MulAction G X]

/-- The finitary site axioms for a split extension, with externally supplied site groups. -/
structure FinitarySite (α : G →* MulAut N) (A : Finset X → Type uA)
    [∀ S, Group (A S)] where
  project : ∀ S, N →* A S
  project_surjective : ∀ S, Function.Surjective (project S)
  residuallyFinite : ∀ S, IsResiduallyFinite (A S)
  empty_subsingleton : Subsingleton (A ∅)
  embed : ∀ {U S : Finset X}, U ⊆ S → A U →* A S
  embed_injective : ∀ {U S : Finset X} (hUS : U ⊆ S), Function.Injective (embed hUS)
  embed_comp : ∀ {V U S : Finset X} (hVU : V ⊆ U) (hUS : U ⊆ S),
    (embed hUS).comp (embed hVU) = embed (Finset.Subset.trans hVU hUS)
  detect : ∀ E : Finset N, (∀ n ∈ E, n ≠ 1) →
    ∃ S, ∀ n ∈ E, project S n ≠ 1
  support : N → Finset X
  finiteSupport : ∀ (n : N) (g : G) {U S : Finset X} (hUS : U ⊆ S),
    (∀ x ∈ support n, g • x ∈ S → g • x ∈ U) →
    project S (α g n) = embed hUS (project U (α g n))
  stabilizer_invariance : ∀ (S : Finset X) (k : G),
    (∀ x ∈ S, k • x = x) → ∀ n, project S (α k n) = project S n

namespace FinitarySite

variable {α : G →* MulAut N} {A : Finset X → Type uA} [∀ S, Group (A S)]
  (D : FinitarySite α A) {Q : Type uQ} [Group Q] {B : Type uB}

/-- Coherent injective inclusions act identically on a site group itself. -/
@[simp] theorem embed_refl (S : Finset X) :
    D.embed (Finset.Subset.refl S) = MonoidHom.id (A S) := by
  apply MonoidHom.ext
  intro a
  apply D.embed_injective (Finset.Subset.refl S)
  exact DFunLike.congr_fun (D.embed_comp (Finset.Subset.refl S) (Finset.Subset.refl S)) a

/-- Coordinates on a finite site quotient and the base group. -/
def quotientCoordinate (S : Finset X) (q : A S →* Q)
    (w : SemidirectProduct N G α) : Q × G := (q (D.project S w.left), w.right)

theorem quotientCoordinate_surjective (S : Finset X) (q : A S →* Q)
    (hq : Function.Surjective q) : Function.Surjective (D.quotientCoordinate S q) := by
  rintro ⟨u, g⟩
  obtain ⟨a, ha⟩ := hq u
  obtain ⟨n, hn⟩ := D.project_surjective S a
  exact ⟨⟨n, g⟩, by simp only [quotientCoordinate, hn, ha]⟩

/-- The fiber multiplier produced by a kernel element at a base coordinate. -/
def coefficient (S : Finset X) (q : A S →* Q) (g : G) (n : N) : Q :=
  q (D.project S (α g n))

theorem quotientCoordinate_mul (S : Finset X) (q : A S →* Q)
    (w m : SemidirectProduct N G α) :
    D.quotientCoordinate S q (w * m) =
      ((D.quotientCoordinate S q w).1 * D.coefficient S q w.right m.left,
        w.right * m.right) := by
  simp only [quotientCoordinate, coefficient, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, map_mul]

/-- The transplanted local map in quotient coordinates. -/
def quotientLocalMap (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (y : Q × G → B) : Q × G → B :=
  fun p ↦ μ (fun m ↦ y (p.1 * D.coefficient S q p.2 m.val.left, p.2 * m.val.right))

theorem quotientLocalMap_intertwining (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B) (y : Q × G → B) :
    localMap M μ (configPullback (D.quotientCoordinate S q) y) =
      configPullback (D.quotientCoordinate S q) (D.quotientLocalMap S q M μ y) := by
  funext w
  apply congrArg μ
  funext m
  exact congrArg y (D.quotientCoordinate_mul S q w m.val)

theorem quotientLocalMap_injective (S : Finset X) (q : A S →* Q)
    (hq : Function.Surjective q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (hτ : Function.Injective (localMap M μ)) :
    Function.Injective (D.quotientLocalMap S q M μ) :=
  transplant_injective (D.quotientCoordinate_surjective S q hq)
    (D.quotientLocalMap_intertwining S q M μ) hτ

/-- Pointwise site stabilizers make the fiber coefficients invariant. -/
theorem coefficient_stabilizer (S : Finset X) (q : A S →* Q) (k g : G)
    (hk : ∀ x ∈ S, k • x = x) (n : N) :
    D.coefficient S q (k * g) n = D.coefficient S q g n := by
  change q (D.project S (α (k * g) n)) = q (D.project S (α g n))
  rw [map_mul]
  exact congrArg q (D.stabilizer_invariance S k hk (α g n))

/-- Finite support is exactly the compatibility of coefficients across site inclusions. -/
theorem coefficient_of_support (S U : Finset X) (hUS : U ⊆ S) (q : A S →* Q)
    (g : G) (n : N) (h : ∀ x ∈ D.support n, g • x ∈ S → g • x ∈ U) :
    D.coefficient S q g n = D.coefficient U (q.comp (D.embed hUS)) g n := by
  exact congrArg q (D.finiteSupport n g hUS h)

/-- The finite-fiber coordinate family separates every finite set of group elements. -/
theorem exists_quotientCoordinate_injOn (F : Finset (SemidirectProduct N G α)) :
    ∃ (S : Finset X) (K : Subgroup (A S)) (hKn : K.Normal),
      letI : K.Normal := hKn
      K.FiniteIndex ∧ Set.InjOn (D.quotientCoordinate S (QuotientGroup.mk' K))
        (F : Set (SemidirectProduct N G α)) := by
  classical
  let E := ((F.product F).image fun p : SemidirectProduct N G α ×
    SemidirectProduct N G α ↦ p.1.left / p.2.left).filter (· ≠ 1)
  obtain ⟨S, hS⟩ := D.detect E (fun n hn ↦ (Finset.mem_filter.mp hn).2)
  let P := E.image (D.project S)
  have hP : ∀ a ∈ P, a ≠ 1 := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    exact hS n hn
  obtain ⟨K, hKn, hKf, hK⟩ :=
    (D.residuallyFinite S).exists_normal_avoiding_finset P hP
  letI := hKn
  refine ⟨S, K, hKn, hKf, ?_⟩
  intro w hw v hv hcoord
  have hright : w.right = v.right := congrArg Prod.snd hcoord
  have hleft : w.left = v.left := by
    by_contra hne
    have hdiv : w.left / v.left ≠ 1 := fun h ↦ hne (div_eq_one.mp h)
    have hE : w.left / v.left ∈ E := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(w, v), Finset.mem_product.mpr ⟨hw, hv⟩, rfl⟩, hdiv⟩
    have hPmem : D.project S (w.left / v.left) ∈ P :=
      Finset.mem_image.mpr ⟨w.left / v.left, hE, rfl⟩
    apply hK _ hPmem
    have hquot := congrArg Prod.fst hcoord
    have hmem : D.project S w.left / D.project S v.left ∈ K :=
      QuotientGroup.eq_iff_div_mem.mp hquot
    simpa only [map_div] using hmem
  exact SemidirectProduct.ext hleft hright

end FinitarySite

end GroupApproximation.Surjunctivity
