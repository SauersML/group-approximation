import GroupApproximation.Dynamics.FinitarySite
import GroupApproximation.Dynamics.FinitarySurjunctivity
import GroupApproximation.Algebra.PermutationalWreath

/-!
# Finitary sites for permutational wreath products

Restriction to finitely many lamp coordinates supplies the finitary site
structure. Lamps may be nonabelian; only residual finiteness is used.
-/

namespace GroupApproximation.Surjunctivity

universe u v w

variable {A : Type u} [Group A] {X : Type v}

/-- Products of residually finite groups are residually finite, by evaluation. -/
theorem isResiduallyFinite_pi (hA : IsResiduallyFinite A) (I : Type v) :
    IsResiduallyFinite (I → A) := by
  classical
  rw [isResiduallyFinite_iff]
  intro f hf
  have hex : ∃ i, f i ≠ 1 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨K, hKn, hKf, hK⟩ := hA.exists_normal_avoiding_finset {f i}
    (by intro a ha; obtain rfl := Finset.mem_singleton.mp ha; exact hi)
  letI := hKn
  letI := hKf
  let ev : (I → A) →* A :=
    { toFun := fun y => y i, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨K.comap ev, finiteIndex_comap_of_normal ev K, ?_⟩
  exact hK (f i) (Finset.mem_singleton_self _) 

/-- Restrict a lamp configuration to the marked sites. -/
def wreathSiteProject (S : Finset X) : Lamp A X →* (S → A) where
  toFun := fun n s => (n : X → A) s
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- Every finite-site configuration extends by the identity lamp. -/
theorem wreathSiteProject_surjective (S : Finset X) :
    Function.Surjective (wreathSiteProject (A := A) S) := by
  classical
  intro a
  let f : X → A := fun x => if hx : x ∈ S then a ⟨x, hx⟩ else 1
  have hf : {x | f x ≠ 1}.Finite := by
    apply S.finite_toSet.subset
    intro x hx
    by_contra hnot
    exact hx (dif_neg hnot)
  refine ⟨⟨f, hf⟩, ?_⟩
  funext s
  exact dif_pos s.property

/-- Include a smaller finite-site group by identity extension. -/
noncomputable def wreathSiteEmbed {U S : Finset X} (_hUS : U ⊆ S) :
    (U → A) →* (S → A) := by
  classical
  exact
    { toFun := fun a s => if hs : (s : X) ∈ U then a ⟨s, hs⟩ else 1
      map_one' := by funext s; split <;> rfl
      map_mul' := by
        intro a b
        funext s
        by_cases hs : (s : X) ∈ U <;> simp [hs] }

theorem wreathSiteEmbed_injective {U S : Finset X} (hUS : U ⊆ S) :
    Function.Injective (wreathSiteEmbed (A := A) hUS) := by
  classical
  intro a b hab
  funext u
  have h := congrFun hab ⟨u, hUS u.property⟩
  simpa only [wreathSiteEmbed, MonoidHom.coe_mk, OneHom.coe_mk,
    dif_pos u.property] using h

theorem wreathSiteEmbed_comp {V U S : Finset X} (hVU : V ⊆ U) (hUS : U ⊆ S) :
    (wreathSiteEmbed (A := A) hUS).comp (wreathSiteEmbed hVU) =
      wreathSiteEmbed (hVU.trans hUS) := by
  classical
  apply MonoidHom.ext
  intro a
  funext s
  by_cases hsV : (s : X) ∈ V
  · have hsU := hVU hsV
    simp [wreathSiteEmbed, hsV, hsU]
  · by_cases hsU : (s : X) ∈ U <;> simp [wreathSiteEmbed, hsV, hsU]

/-- The finite set of nonidentity lamp coordinates. -/
noncomputable def wreathSiteSupport (n : Lamp A X) : Finset X := n.property.toFinset

@[simp] theorem mem_wreathSiteSupport (n : Lamp A X) (s : X) :
    s ∈ wreathSiteSupport n ↔ (n : X → A) s ≠ 1 := Set.Finite.mem_toFinset _

theorem wreathSiteProject_detect (E : Finset (Lamp A X))
    (hE : ∀ n ∈ E, n ≠ 1) :
    ∃ S : Finset X, ∀ n ∈ E, wreathSiteProject S n ≠ 1 := by
  classical
  let S := E.biUnion wreathSiteSupport
  refine ⟨S, ?_⟩
  intro n hn heq
  apply hE n hn
  apply Subtype.ext
  funext x
  by_cases hx : (n : X → A) x = 1
  · exact hx
  · have hxS : x ∈ S := Finset.mem_biUnion.mpr
      ⟨n, hn, (mem_wreathSiteSupport n x).mpr hx⟩
    exact congrFun heq ⟨x, hxS⟩

variable {G : Type w} [Group G] [MulAction G X]

theorem wreathSiteProject_support (n : Lamp A X) (g : G)
    {U S : Finset X} (hUS : U ⊆ S)
    (h : ∀ x ∈ wreathSiteSupport n, g • x ∈ S → g • x ∈ U) :
    wreathSiteProject S (lampActionHom g n) =
      wreathSiteEmbed hUS (wreathSiteProject U (lampActionHom g n)) := by
  classical
  funext s
  by_cases hsU : (s : X) ∈ U
  · simp [wreathSiteProject, wreathSiteEmbed, hsU]
  · have hn : (n : X → A) (g⁻¹ • (s : X)) = 1 := by
      by_contra hne
      have hx := h (g⁻¹ • (s : X)) ((mem_wreathSiteSupport n _).mpr hne)
      simp only [smul_inv_smul] at hx
      exact hsU (hx s.property)
    simpa [wreathSiteProject, wreathSiteEmbed, hsU, lampActionHom, lampAut] using hn

theorem wreathSiteProject_stabilizer (S : Finset X) (k : G)
    (hk : ∀ x ∈ S, k • x = x) (n : Lamp A X) :
    wreathSiteProject S (lampActionHom k n) = wreathSiteProject S n := by
  funext s
  have hs : k⁻¹ • (s : X) = (s : X) := by
    calc
      k⁻¹ • (s : X) = k⁻¹ • (k • (s : X)) := congrArg (fun x => k⁻¹ • x) (hk s s.property).symm
      _ = (s : X) := inv_smul_smul k (s : X)
  change (n : X → A) (k⁻¹ • (s : X)) = (n : X → A) s
  rw [hs]

/-- The residually finite lamp wreath carries the finitary structure used
by the surjunctivity permanence theorem. -/
noncomputable def wreathFinitarySite (hA : IsResiduallyFinite A) :
    FinitarySite (lampActionHom (K := A) (G := G) (X := X)) (fun S : Finset X => S → A) where
  project := wreathSiteProject
  project_surjective := wreathSiteProject_surjective
  residuallyFinite := fun S => isResiduallyFinite_pi hA S
  empty_subsingleton := inferInstance
  embed := wreathSiteEmbed
  embed_injective := wreathSiteEmbed_injective
  embed_comp := wreathSiteEmbed_comp
  detect := wreathSiteProject_detect
  support := wreathSiteSupport
  finiteSupport := wreathSiteProject_support
  stabilizer_invariance := wreathSiteProject_stabilizer

/-- A permutational wreath product with residually finite lamps is
surjunctive exactly when its base group is surjunctive, for every site action. -/
theorem isSurjunctive_wreath_iff (hA : IsResiduallyFinite A) :
    IsSurjunctive (Wreath A G X) ↔ IsSurjunctive G :=
  (wreathFinitarySite (G := G) (X := X) hA).isSurjunctive_iff

theorem isSurjunctive_wreath (hA : IsResiduallyFinite A) (hG : IsSurjunctive G) :
    IsSurjunctive (Wreath A G X) := (isSurjunctive_wreath_iff hA).mpr hG

end GroupApproximation.Surjunctivity
