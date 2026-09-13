import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Schreier
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.GroupTheory.FinitePresentationExtension
import GroupApproximation.TypeA2.Statement

/-!
# Type [A₂] passes to extensions

Let `Γ →ι G →π H` be a short exact sequence of groups: `ι` is injective, `π` is surjective and
`ker π = range ι`.  Let `Γ` and `G` act on a set `X` compatibly, `ι γ • x = γ • x`.  This module
shows that the three conditions of type [A₂] pass from `Γ` to `G` when `H` is finitely presented.

* `isFinitelyPresented_of_exact`: `G` is finitely presented when `Γ` and `H` are.
* `stabilizer_fg_of_exact`: `Stab_G(x)` is finitely generated when `G` is finitely generated,
  `Stab_Γ(x)` is finitely generated and `Γ` has finitely many orbits on `X`.  The kernel part
  `Stab_G(x) ∩ ker π` is the image of `Stab_Γ(x)`.  The image part `π(Stab_G(x))` equals
  `π(Stab_G(Γx))`, and `Stab_G(Γx)` has finite index in `G` because `G` permutes the finitely
  many `Γ`-orbits; Schreier's lemma makes it finitely generated.
* `finite_orbitRel_quotient_of_compat`: `G` has finitely many orbits where `Γ` does.
* `isTypeA2_of_exact`: type [A₂] passes from `Γ ↷ S` to `G ↷ S`.

Two subgroup facts are proved on the way: images of finitely generated subgroups are finitely
generated (`fg_map_of_fg`), and a subgroup is finitely generated when its image and its
intersection with the kernel are (`fg_of_fg_map_of_fg_inf_ker`).
-/

open MulAction Pointwise

namespace GroupApproximation.TypeA2

section Subgroups

variable {G H : Type*} [Group G] [Group H]

/-- The image of a finitely generated subgroup is finitely generated. -/
theorem fg_map_of_fg {A : Subgroup G} (hA : A.FG) (f : G →* H) : (A.map f).FG := by
  classical
  obtain ⟨T, hT⟩ := hA
  exact ⟨T.image f, by rw [Finset.coe_image, ← MonoidHom.map_closure, hT]⟩

/-- A subgroup is finitely generated when its image under `π` and its intersection with
`ker π` are. -/
theorem fg_of_fg_map_of_fg_inf_ker {A : Subgroup G} (π : G →* H) (hmap : (A.map π).FG)
    (hker : (A ⊓ π.ker).FG) : A.FG := by
  obtain ⟨T, hT⟩ := hmap
  obtain ⟨U, hU⟩ := hker
  have hTsub : (T : Set H) ⊆ π '' (A : Set G) := by
    intro t ht
    have h : t ∈ A.map π := by
      rw [← hT]
      exact Subgroup.subset_closure ht
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨a, ha, rfl⟩
  obtain ⟨T', hT'A, hT'fin, hT'img⟩ := (Set.exists_subset_image_finite_and
    (p := fun t => t = (T : Set H))).mp ⟨(T : Set H), hTsub, T.finite_toSet, rfl⟩
  rw [Subgroup.fg_iff]
  refine ⟨T' ∪ (U : Set G), le_antisymm ?_ ?_, hT'fin.union U.finite_toSet⟩
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hT'A hx
    · have h : x ∈ A ⊓ π.ker := by
        rw [← hU]
        exact Subgroup.subset_closure hx
      exact (Subgroup.mem_inf.mp h).1
  · intro a ha
    have hπa : π a ∈ (Subgroup.closure T').map π := by
      rw [MonoidHom.map_closure, hT'img, hT]
      exact Subgroup.mem_map_of_mem π ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hπa
    have hbA : b ∈ A := (Subgroup.closure_le A).mpr hT'A hb
    have hk : b⁻¹ * a ∈ A ⊓ π.ker := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hbA) ha, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, inv_mul_cancel]
    rw [← hU] at hk
    have hb' : b ∈ Subgroup.closure (T' ∪ (U : Set G)) :=
      Subgroup.closure_mono Set.subset_union_left hb
    have hk' : b⁻¹ * a ∈ Subgroup.closure (T' ∪ (U : Set G)) :=
      Subgroup.closure_mono Set.subset_union_right hk
    have h := mul_mem hb' hk'
    rwa [mul_inv_cancel_left] at h

variable {Γ : Type*} [Group Γ]

/-- The middle term of a short exact sequence of finitely generated groups is finitely
generated. -/
theorem fg_of_exact [Group.FG Γ] [Group.FG H] (ι : Γ →* G) (π : G →* H)
    (hπ : Function.Surjective π) (hex : π.ker = ι.range) : Group.FG G := by
  refine Group.fg_def.mpr (fg_of_fg_map_of_fg_inf_ker π ?_ ?_)
  · rw [Subgroup.map_top_of_surjective π hπ]
    exact Group.fg_def.mp inferInstance
  · rw [top_inf_eq, hex, MonoidHom.range_eq_map]
    exact fg_map_of_fg (Group.fg_def.mp inferInstance) ι

/-- The middle term of a short exact sequence of finitely presented groups is finitely
presented. -/
theorem isFinitelyPresented_of_exact [Group.IsFinitelyPresented Γ]
    [Group.IsFinitelyPresented H] (ι : Γ →* G) (π : G →* H) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : π.ker = ι.range) : Group.IsFinitelyPresented G := by
  haveI : Group.IsFinitelyPresented π.ker := Group.IsFinitelyPresented.equiv
    ((MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hex.symm))
  haveI : Group.IsFinitelyPresented (G ⧸ π.ker) :=
    Group.IsFinitelyPresented.equiv (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm
  exact FinitePresentationExtension.isFinitelyPresented_of_normal π.ker

end Subgroups

section Orbits

variable {Γ G X : Type*} [Group Γ] [Group G] [MulAction Γ X] [MulAction G X]

/-- If `ι : Γ →* G` is compatible with the actions, `G` has finitely many orbits where `Γ`
does. -/
theorem finite_orbitRel_quotient_of_compat (ι : Γ →* G)
    (hι : ∀ (γ : Γ) (x : X), ι γ • x = γ • x) (h : Finite (orbitRel.Quotient Γ X)) :
    Finite (orbitRel.Quotient G X) := by
  obtain ⟨F, hF⟩ := finite_orbitRel_quotient_iff.mp h
  refine finite_orbitRel_quotient_iff.mpr ⟨F, fun x => ?_⟩
  obtain ⟨f, hf, γ, hγ⟩ := hF x
  exact ⟨f, hf, ι γ, (hι γ f).trans hγ⟩

/-- Finitely many orbits on `X × X` give finitely many orbits on `X`. -/
theorem finite_orbitRel_quotient_of_prod (h : Finite (orbitRel.Quotient G (X × X))) :
    Finite (orbitRel.Quotient G X) := by
  classical
  obtain ⟨F, hF⟩ := finite_orbitRel_quotient_iff.mp h
  refine finite_orbitRel_quotient_iff.mpr ⟨F.image Prod.fst, fun x => ?_⟩
  obtain ⟨f, hf, g, hg⟩ := hF (x, x)
  exact ⟨f.1, Finset.mem_image_of_mem _ hf, g, congrArg Prod.fst hg⟩

/-- A point in the orbit of a point with finitely generated stabilizer has finitely generated
stabilizer. -/
theorem stabilizer_fg_of_mem_orbit {x y : X} (hy : y ∈ orbit G x) (hx : (stabilizer G x).FG) :
    (stabilizer G y).FG := by
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hy
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact fg_map_of_fg hx _

variable {H : Type*} [Group H]

/-- **Stabilizers in an extension.**  Let `ker π = range ι` with `ι` compatible with the
actions, and let `Γ` have finitely many orbits on `X`.  If `G` is finitely generated and
`Stab_Γ(x)` is finitely generated, so is `Stab_G(x)`. -/
theorem stabilizer_fg_of_exact [Group.FG G] (ι : Γ →* G) (π : G →* H) (hex : π.ker = ι.range)
    (hι : ∀ (γ : Γ) (x : X), ι γ • x = γ • x) (hfin : Finite (orbitRel.Quotient Γ X)) (x : X)
    (hstab : (stabilizer Γ x).FG) : (stabilizer G x).FG := by
  have hmemker : ∀ γ : Γ, ι γ ∈ π.ker := fun γ => by
    rw [hex]
    exact MonoidHom.mem_range.mpr ⟨γ, rfl⟩
  have hker : stabilizer G x ⊓ π.ker = (stabilizer Γ x).map ι := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgx, hgk⟩ := Subgroup.mem_inf.mp hg
      rw [hex] at hgk
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hgk
      refine Subgroup.mem_map_of_mem ι ?_
      rw [mem_stabilizer_iff, ← hι γ x]
      exact mem_stabilizer_iff.mp hgx
    · intro g hg
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, hmemker γ⟩
      rw [mem_stabilizer_iff, hι γ x]
      exact mem_stabilizer_iff.mp hγ
  have hconj : ∀ (g : G) (γ : Γ), ∃ δ : Γ, ι δ = g * ι γ * g⁻¹ := by
    intro g γ
    have hmem : g * ι γ * g⁻¹ ∈ π.ker := (MonoidHom.normal_ker π).conj_mem (ι γ) (hmemker γ) g
    rw [hex] at hmem
    exact MonoidHom.mem_range.mp hmem
  have hsmul : ∀ (g : G) (y : X), g • orbit Γ y = orbit Γ (g • y) := by
    intro g y
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hz
      obtain ⟨γ, rfl⟩ := mem_orbit_iff.mp hw
      obtain ⟨δ, hδ⟩ := hconj g γ
      refine mem_orbit_iff.mpr ⟨δ, ?_⟩
      rw [← hι δ (g • y), ← hι γ y, hδ, mul_smul, mul_smul, inv_smul_smul]
    · intro hz
      obtain ⟨δ, rfl⟩ := mem_orbit_iff.mp hz
      obtain ⟨δ', hδ'⟩ := hconj g⁻¹ δ
      refine Set.mem_smul_set.mpr ⟨δ' • y, mem_orbit y δ', ?_⟩
      rw [← hι δ' y, ← hι δ (g • y), hδ', mul_smul, mul_smul, smul_inv_smul, inv_inv]
  have hO : (orbit G (orbit Γ x)).Finite := by
    haveI := hfin
    refine (Set.finite_range fun q : orbitRel.Quotient Γ X => orbitRel.Quotient.orbit q).subset ?_
    intro O hO
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hO
    exact ⟨Quotient.mk _ (g • x), (hsmul g x).symm⟩
  have hidx : (stabilizer G (orbit Γ x)).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, index_stabilizer]
    exact Set.ncard_ne_zero_of_mem (mem_orbit_self _) hO
  have hfg : (stabilizer G (orbit Γ x)).FG := by
    haveI := hidx
    exact (Group.fg_iff_subgroup_fg _).mp (Subgroup.fg_of_index_ne_zero _)
  have hmapeq : (stabilizer G x).map π = (stabilizer G (orbit Γ x)).map π := by
    apply le_antisymm
    · apply Subgroup.map_mono
      intro g hg
      rw [mem_stabilizer_iff, hsmul, mem_stabilizer_iff.mp hg]
    · intro k hk
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hk
      have hgx : g • x ∈ orbit Γ x := by
        have h : g • x ∈ orbit Γ (g • x) := mem_orbit_self _
        rwa [← hsmul, mem_stabilizer_iff.mp hg] at h
      obtain ⟨γ, hγ⟩ := mem_orbit_iff.mp hgx
      refine Subgroup.mem_map.mpr ⟨(ι γ)⁻¹ * g, ?_, ?_⟩
      · rw [mem_stabilizer_iff, mul_smul, ← hγ, ← hι γ x, inv_smul_smul]
      · rw [map_mul, map_inv, MonoidHom.mem_ker.mp (hmemker γ), inv_one, one_mul]
  have hmapfg : ((stabilizer G x).map π).FG := by
    rw [hmapeq]
    exact fg_map_of_fg hfg π
  have hkerfg : (stabilizer G x ⊓ π.ker).FG := by
    rw [hker]
    exact fg_map_of_fg hstab ι
  exact fg_of_fg_map_of_fg_inf_ker π hmapfg hkerfg

end Orbits

/-- **Type [A₂] passes to extensions.**  Let `Γ →ι G →π H` be short exact, with `ι` compatible
with actions of `Γ` and `G` on `S`.  If `Γ ↷ S` is of type [A₂] and `H` is finitely presented,
then `G ↷ S` is of type [A₂]. -/
theorem isTypeA2_of_exact {Γ G H S : Type} [Group Γ] [Group G] [Group H] [MulAction Γ S]
    [MulAction G S] [Group.IsFinitelyPresented H] (ι : Γ →* G) (π : G →* H)
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hex : π.ker = ι.range)
    (hcompat : ∀ (γ : Γ) (s : S), ι γ • s = γ • s) (hΓ : IsTypeA2 Γ S) : IsTypeA2 G S := by
  obtain ⟨hne, hfp, hstab, horb⟩ := hΓ
  haveI := hfp
  have hG : Group.IsFinitelyPresented G := isFinitelyPresented_of_exact ι π hι hπ hex
  haveI := hG
  haveI : Group.FG G := ProductFinitePresentation.fg_of_isFinitelyPresented G
  refine ⟨hne, hG, fun s => ?_, ?_⟩
  · exact stabilizer_fg_of_exact ι π hex hcompat (finite_orbitRel_quotient_of_prod horb) s
      (hstab s)
  · exact finite_orbitRel_quotient_of_compat ι
      (fun γ p => Prod.ext (hcompat γ p.1) (hcompat γ p.2)) horb

end GroupApproximation.TypeA2
