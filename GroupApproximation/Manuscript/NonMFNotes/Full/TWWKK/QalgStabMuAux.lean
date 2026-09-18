import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabMatEmbed

/-!
# Entrywise `⋆`-homomorphisms of `𝒦 ⊗ -`

Auxiliary facts about `⋆`-homomorphisms `G : 𝒦 ⊗ X → 𝒦 ⊗ Y` acting entrywise on the matrix
units, `G (e_{ij} ⊗ x) = e_{ij} ⊗ f x`, used to build Cuntz's comparison map
`μ : q(𝒦 ⊗ B) → 𝒦 ⊗ qB` (`QalgStabMuCore`):

* `induction_single`: closed induction on `𝒦 ⊗ B` from the matrix units `e_{ij} ⊗ b`;
* `hom_ext_single`: `⋆`-homomorphisms out of `𝒦 ⊗ B` agreeing on matrix units are equal;
* `entry_map_of_single`, `injective_of_single`: an entrywise map is injective when `f` is;
* `mul_mem_range`: if the range of `f` is a two-sided ideal, so is the range of `G`.

Source: J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1 (proof of
Proposition 1.6).
Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C2b-2, work order WO-TWWKK-C2b-2).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

open Filter Topology

namespace MuAux

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-- `⋆`-homomorphisms between C⋆-algebras are continuous (they are contractive). -/
theorem continuous_hom {X Y : Type*} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (k : X →⋆ₙₐ[ℂ] Y) : Continuous fun x : X => k x :=
  AddMonoidHomClass.continuous_of_bound k 1 fun x => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le k x

/-- An injective `⋆`-homomorphism of C⋆-algebras is isometric, so it has closed range. -/
theorem isClosed_range_hom {X Y : Type*} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (k : X →⋆ₙₐ[ℂ] Y) (hk : Function.Injective k) : IsClosed (Set.range k) :=
  (AddMonoidHomClass.isometry_of_norm k
    (NonUnitalStarAlgHom.norm_map k hk)).isClosedEmbedding.isClosed_range

/-- The entries of a matrix unit: `(e_{ij} ⊗ b)_{kl} = δ_{ki} δ_{lj} b`. -/
theorem entry_single (k l i j : ℕ) (b : B) :
    Stab.entry k l (Stab.single i j b) = if k = i ∧ l = j then b else 0 :=
  Stab.rep_injective B <| by
    rw [Stab.rep_entry, Stab.coe_single, Stab.compress_matUnit]
    by_cases h : k = i ∧ l = j
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, map_zero]

theorem coe_ofMat_entryMatrix (N : ℕ) (x : Stab B) :
    ((Stab.ofMat B N (Stab.entryMatrix N x) : Stab B) : Stab.Ambient B) =
      Stab.trunc B N * (x : Stab.Ambient B) * Stab.trunc B N := by
  rw [← Stab.matEmbed_entryMatrix, Stab.ofMat_apply, Stab.matEmbed_apply, Stab.coe_sum]
  exact Finset.sum_congr rfl fun i _ => Stab.coe_sum _ _

/-- The upper-left blocks `Σ_{i,j<N} e_{ij} ⊗ x_{ij}` of `x ∈ 𝒦 ⊗ B` converge to `x`. -/
theorem tendsto_ofMat_entryMatrix (x : Stab B) :
    Tendsto (fun N => Stab.ofMat B N (Stab.entryMatrix N x)) atTop (𝓝 x) :=
  tendsto_subtype_rng.mpr <| Tendsto.congr (fun N => (coe_ofMat_entryMatrix N x).symm)
    (Stab.tendsto_trunc_mul_mul_trunc x.2)

/-- **Closed induction on `𝒦 ⊗ B`**: a closed additive property of the matrix units
`e_{ij} ⊗ b` holds everywhere. -/
theorem induction_single {p : Stab B → Prop} (hp : IsClosed {x | p x})
    (hsingle : ∀ (i j : ℕ) (b : B), p (Stab.single i j b))
    (hadd : ∀ x y, p x → p y → p (x + y)) (x : Stab B) : p x := by
  have h0 : p 0 := by
    have h := hsingle 0 0 0
    rwa [Stab.single_zero] at h
  have hmat : ∀ (N : ℕ) (M : CStarMatrix (Fin N) (Fin N) B), p (Stab.ofMat B N M) := by
    intro N M
    rw [Stab.ofMat_apply]
    exact Finset.sum_induction _ p hadd h0 fun i _ =>
      Finset.sum_induction _ p hadd h0 fun j _ => hsingle i j (M i j)
  exact hp.mem_of_tendsto (tendsto_ofMat_entryMatrix x)
    (Eventually.of_forall fun N => hmat N (Stab.entryMatrix N x))

/-- Two `⋆`-homomorphisms out of `𝒦 ⊗ B` agreeing on the matrix units are equal. -/
theorem hom_ext_single {Y : Type*} [NonUnitalCStarAlgebra Y] {F G : Stab B →⋆ₙₐ[ℂ] Y}
    (h : ∀ (i j : ℕ) (b : B), F (Stab.single i j b) = G (Stab.single i j b)) : F = G :=
  NonUnitalStarAlgHom.ext fun x => by
    refine induction_single ?_ ?_ ?_ x
    · exact isClosed_eq (continuous_hom F) (continuous_hom G)
    · intro i j b
      exact h i j b
    · intro y z hy hz
      rw [map_add, map_add, hy, hz]

/-- Elements of `𝒦 ⊗ B` with the same entries are equal. -/
theorem ext_entry {x y : Stab B} (h : ∀ i j : ℕ, Stab.entry i j x = Stab.entry i j y) :
    x = y := by
  have hxy : ∀ N : ℕ, Stab.entryMatrix N x = Stab.entryMatrix N y := fun N =>
    CStarMatrix.ext fun i j => h i j
  exact tendsto_nhds_unique (tendsto_ofMat_entryMatrix x)
    ((tendsto_ofMat_entryMatrix y).congr fun N =>
      congrArg (fun M => Stab.ofMat B N M) (hxy N).symm)

section Entrywise

variable {X Y : Type u} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]

/-- An entrywise map acts on the entries: `(G x)_{kl} = f (x_{kl})`. -/
theorem entry_map_of_single (f : X →⋆ₙₐ[ℂ] Y) (G : Stab X →⋆ₙₐ[ℂ] Stab Y)
    (hG : ∀ (i j : ℕ) (b : X), G (Stab.single i j b) = Stab.single i j (f b)) (k l : ℕ)
    (x : Stab X) : Stab.entry k l (G x) = f (Stab.entry k l x) := by
  refine induction_single ?_ ?_ ?_ x
  · exact isClosed_eq ((Stab.continuous_entry k l).comp (continuous_hom G))
      ((continuous_hom f).comp (Stab.continuous_entry k l))
  · intro i j b
    rw [hG, entry_single, entry_single]
    by_cases h : k = i ∧ l = j
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, map_zero]
  · intro y z hy hz
    rw [map_add, Stab.entry_add, Stab.entry_add, hy, hz, map_add]

/-- An entrywise map induced by an injective `f` is injective. -/
theorem injective_of_single (f : X →⋆ₙₐ[ℂ] Y) (hf : Function.Injective f)
    (G : Stab X →⋆ₙₐ[ℂ] Stab Y)
    (hG : ∀ (i j : ℕ) (b : X), G (Stab.single i j b) = Stab.single i j (f b)) :
    Function.Injective G := fun x y h => ext_entry fun i j => hf <| by
  rw [← entry_map_of_single f G hG, ← entry_map_of_single f G hG, h]

/-- **Ideals are preserved**: if the range of `f` is a two-sided ideal of `Y` and the range of
the entrywise map `G` is closed, then the range of `G` is a two-sided ideal of `𝒦 ⊗ Y`. -/
theorem mul_mem_range (f : X →⋆ₙₐ[ℂ] Y) (G : Stab X →⋆ₙₐ[ℂ] Stab Y)
    (hG : ∀ (i j : ℕ) (b : X), G (Stab.single i j b) = Stab.single i j (f b))
    (hR : IsClosed (Set.range G)) (hl : ∀ (a : Y) (b : X), ∃ w, f w = a * f b)
    (hr : ∀ (a : Y) (b : X), ∃ w, f w = f b * a) (s : Stab Y) (y : Stab X) :
    s * G y ∈ Set.range G ∧ G y * s ∈ Set.range G := by
  have hadd : ∀ u v : Stab Y, u ∈ Set.range G → v ∈ Set.range G → u + v ∈ Set.range G := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add G a b⟩
  have hzero : (0 : Stab Y) ∈ Set.range G := ⟨0, map_zero G⟩
  have hsingle : ∀ (i j : ℕ) (a : Y) (y : Stab X),
      Stab.single i j a * G y ∈ Set.range G ∧ G y * Stab.single i j a ∈ Set.range G := by
    intro i j a y
    refine induction_single ?_ ?_ ?_ y
    · have h1 := hR.preimage ((continuous_const_mul (Stab.single i j a)).comp (continuous_hom G))
      have h2 := hR.preimage ((continuous_mul_const (Stab.single i j a)).comp (continuous_hom G))
      exact h1.inter h2
    · intro k l b
      rw [hG, Stab.single_mul_single, Stab.single_mul_single]
      obtain ⟨w₁, hw₁⟩ := hl a b
      obtain ⟨w₂, hw₂⟩ := hr a b
      constructor
      · by_cases h : j = k
        · rw [if_pos h, ← hw₁]
          exact ⟨Stab.single i l w₁, hG i l w₁⟩
        · rw [if_neg h]
          exact hzero
      · by_cases h : l = i
        · rw [if_pos h, ← hw₂]
          exact ⟨Stab.single k j w₂, hG k j w₂⟩
        · rw [if_neg h]
          exact hzero
    · intro u v hu hv
      rw [map_add, mul_add, add_mul]
      exact ⟨hadd _ _ hu.1 hv.1, hadd _ _ hu.2 hv.2⟩
  have hclosed : IsClosed
      {s : Stab Y | ∀ y : Stab X, s * G y ∈ Set.range G ∧ G y * s ∈ Set.range G} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun y =>
      (hR.preimage (continuous_mul_const (G y))).inter (hR.preimage (continuous_const_mul (G y)))
  revert y
  refine induction_single hclosed ?_ ?_ s
  · exact hsingle
  · intro u v hu hv y
    rw [add_mul, mul_add]
    exact ⟨hadd _ _ (hu y).1 (hv y).1, hadd _ _ (hu y).2 (hv y).2⟩

end Entrywise

end MuAux

end

end GroupApproximation.Full.TWWKK
