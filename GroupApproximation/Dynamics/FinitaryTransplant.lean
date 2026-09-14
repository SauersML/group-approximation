import GroupApproximation.Dynamics.FinitarySite
import GroupApproximation.Dynamics.CosetSlice
import GroupApproximation.Dynamics.FiniteMemory
import GroupApproximation.Dynamics.SiteStrata

/-!
# Common finite-fiber transplants for finitary sites

The quotient homomorphism in a transplanted local map need not be onto its
ambient fiber group: its image acts on each left coset, and canonical coset
extension preserves injectivity. Currying gives uniformly finite-memory
maps on the common alphabet `Q → B`, as needed by marked-site peeling.
-/

namespace GroupApproximation.Surjunctivity

universe uN uG uX uA uQ uB

variable {N : Type uN} {G : Type uG} {X : Type uX}
  [Group N] [Group G] [MulAction G X]
  {α : G →* MulAut N} {A : Finset X → Type uA} [∀ S, Group (A S)]
  {Q : Type uQ} [Group Q] {B : Type uB}

namespace FinitarySite

variable (D : FinitarySite α A)

theorem quotientLocalMap_fiberEquivariant (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B) :
    FiberEquivariant (D.quotientLocalMap S q M μ) := by
  intro a y
  funext p
  apply congrArg μ
  funext m
  simp only [fiberTranslate, mul_assoc]

/-- Enlarging the fiber group is exactly canonical extension from the image. -/
theorem quotientLocalMap_eq_cosetExtension (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B) :
    D.quotientLocalMap S q M μ =
      cosetExtension q.range.subtype (D.quotientLocalMap S q.rangeRestrict M μ) := by
  funext y p
  apply congrArg μ
  funext m
  simp only [cosetSlice, coefficient, one_mul]
  rfl

/-- Injectivity holds in any ambient fiber group, even for a nonsurjective quotient map. -/
theorem quotientLocalMap_injective_any (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (hτ : Function.Injective (localMap M μ)) :
    Function.Injective (D.quotientLocalMap S q M μ) := by
  rw [D.quotientLocalMap_eq_cosetExtension S q M μ]
  exact cosetExtension_injective q.range.subtype
    (D.quotientLocalMap_fiberEquivariant S q.rangeRestrict M μ)
    (D.quotientLocalMap_injective S q.rangeRestrict q.rangeRestrict_surjective M μ hτ)

/-- The same map viewed as a full shift on the common fiber alphabet. -/
def quotientCurried (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (y : G → Q → B) : G → Q → B :=
  fun g u ↦ μ (fun m ↦ y (g * m.val.right) (u * D.coefficient S q g m.val.left))

theorem quotientCurried_injective (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (hτ : Function.Injective (localMap M μ)) :
    Function.Injective (D.quotientCurried S q M μ) := by
  intro y z hyz
  have huncurry : (fun p : Q × G ↦ y p.2 p.1) = fun p : Q × G ↦ z p.2 p.1 := by
    apply D.quotientLocalMap_injective_any S q M μ hτ
    funext p
    exact congrFun (congrFun hyz p.2) p.1
  funext g u
  exact congrFun huncurry (u, g)

theorem quotientLocalMap_surjective_of_curried (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (hτ : Function.Surjective (D.quotientCurried S q M μ)) :
    Function.Surjective (D.quotientLocalMap S q M μ) := by
  intro y
  obtain ⟨z, hz⟩ := hτ (fun g u ↦ y (u, g))
  refine ⟨fun p ↦ z p.2 p.1, ?_⟩
  funext p
  exact congrFun (congrFun hz p.2) p.1

/-- A concrete common memory, containing one, for the curried local map. -/
noncomputable def quotientWindow (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B) : WindowMap G (Q → B) := by
  classical
  exact
    { toFun := D.quotientCurried S q M μ
      memory := insert 1 (M.image SemidirectProduct.right)
      one_mem := Finset.mem_insert_self _ _
      hasMemory := by
        intro y z g h
        funext u
        apply congrArg μ
        funext m
        exact congrFun (h m.val.right (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨m.val, m.property, rfl⟩)))
          (u * D.coefficient S q g m.val.left) }

theorem quotientCurried_stabilizer (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (k : siteStabilizer (G := G) S) (y : G → Q → B) (g : G) :
    D.quotientCurried S q M μ (shift (k : G) y) g =
      D.quotientCurried S q M μ y ((k : G) * g) := by
  funext u
  apply congrArg μ
  funext m
  simp only [shift, mul_assoc,
    D.coefficient_stabilizer S q k g k.property]

/-- All kernel supports appearing in a local rule. -/
noncomputable def memorySites (M : Finset (SemidirectProduct N G α)) : Finset X := by
  classical
  exact M.biUnion fun m ↦ D.support m.left

/-- Away from removed-site strata, a local rule agrees with its smaller-site rule. -/
theorem quotientCurried_compatible (U V : Finset X) (hVU : V ⊆ U) (q : A U →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (y : G → Q → B) (g : G)
    (haway : ∀ s ∈ U, s ∉ V → g ∉ siteStratum (D.memorySites M) s) :
    D.quotientCurried U q M μ y g =
      D.quotientCurried V (q.comp (D.embed hVU)) M μ y g := by
  classical
  funext u
  apply congrArg μ
  funext m
  have hc : D.coefficient U q g m.val.left =
      D.coefficient V (q.comp (D.embed hVU)) g m.val.left := by
    apply D.coefficient_of_support U V hVU q
    intro x hx hxin
    by_contra hxout
    apply haway (g • x) hxin hxout
    change g⁻¹ • (g • x) ∈ D.memorySites M
    rw [inv_smul_smul]
    exact Finset.mem_biUnion.mpr ⟨m.val, m.property, hx⟩
  exact congrArg (y (g * m.val.right)) (congrArg (u * ·) hc)

end FinitarySite

/-- A finite subset of the subtype of a fixed finite site set, viewed in the original site type. -/
def boundedSites (S : Finset X) (U : Finset S) : Finset X :=
  U.map (Function.Embedding.subtype (fun x ↦ x ∈ S))

theorem boundedSites_subset (S : Finset X) (U : Finset S) : boundedSites S U ⊆ S := by
  intro x hx
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hx
  exact u.property

theorem boundedSites_mono (S : Finset X) {U V : Finset S} (hUV : U ⊆ V) :
    boundedSites S U ⊆ boundedSites S V := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
  exact Finset.mem_map.mpr ⟨u, hUV hu, rfl⟩

@[simp] theorem mem_boundedSites (S : Finset X) (U : Finset S) (s : S) :
    (s : X) ∈ boundedSites S U ↔ s ∈ U := by
  simp [boundedSites]

@[simp] theorem boundedSites_univ (S : Finset X) : boundedSites S Finset.univ = S := by
  ext x
  simp [boundedSites]

namespace FinitarySite

variable (D : FinitarySite α A)

/-- Restrict the fixed quotient to a subset of its marked sites. -/
def boundedQuotient (S : Finset X) (q : A S →* Q) (U : Finset S) :
    A (boundedSites S U) →* Q := q.comp (D.embed (boundedSites_subset S U))

theorem boundedQuotient_comp (S : Finset X) (q : A S →* Q)
    {U V : Finset S} (hVU : V ⊆ U) :
    (D.boundedQuotient S q U).comp (D.embed (boundedSites_mono S hVU)) =
      D.boundedQuotient S q V := by
  unfold boundedQuotient
  rw [MonoidHom.comp_assoc, D.embed_comp]

/-- The family of local maps on one common fiber alphabet. -/
noncomputable def boundedWindow (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (U : Finset S) : WindowMap G (Q → B) :=
  D.quotientWindow (boundedSites S U) (D.boundedQuotient S q U) M μ

theorem boundedWindow_compatible (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    {U V : Finset S} (hVU : V ⊆ U) (y : G → Q → B) (g : G)
    (haway : ∀ s ∈ U, s ∉ V → g ∉ siteStratum (D.memorySites M) (s : X)) :
    (D.boundedWindow S q M μ U).toFun y g =
      (D.boundedWindow S q M μ V).toFun y g := by
  change D.quotientCurried (boundedSites S U) (D.boundedQuotient S q U) M μ y g =
    D.quotientCurried (boundedSites S V) (D.boundedQuotient S q V) M μ y g
  rw [← D.boundedQuotient_comp S q hVU]
  apply D.quotientCurried_compatible _ _ (boundedSites_mono S hVU)
  intro x hx hxnot
  obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hx
  apply haway s hs
  intro hsin
  exact hxnot ((mem_boundedSites S V s).mpr hsin)

end FinitarySite

end GroupApproximation.Surjunctivity
