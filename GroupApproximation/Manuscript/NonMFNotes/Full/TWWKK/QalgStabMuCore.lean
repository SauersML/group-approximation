import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Qalg
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgStabMuAux

/-!
# Cuntz's comparison map `μ : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`, for an abstract entrywise functor

Let `S` be any assignment `f ↦ S.map f : 𝒦 ⊗ X → 𝒦 ⊗ Y` acting entrywise on matrix units,
`S.map f (e_{ij} ⊗ x) = e_{ij} ⊗ f x` (a `StabFunctor`; the intended one is `f ↦ id_𝒦 ⊗ f`).
Following Cuntz, the two `⋆`-homomorphisms `S.map ι, S.map ῑ : 𝒦 ⊗ B → 𝒦 ⊗ (B * B)` form a
quasihomomorphism into the closed ideal `𝒦 ⊗ qB` (embedded via `S.map (qB ↪ B * B)`), since
`S.map ι (e_{ij} ⊗ b) - S.map ῑ (e_{ij} ⊗ b) = e_{ij} ⊗ q b`.  The universal property of
`q(𝒦 ⊗ B)` (`Qalg.lift`) gives `μ : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`, characterized by `emb_mu`.

The laws of `μ` (compatibility with `π` and naturality) are in `QalgStabMuLaws`.

Source: J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1 (proof of
Proposition 1.6); arXiv:2404.06840, §3.
Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C2b-2, work order WO-TWWKK-C2b-2).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

open FreeProd

namespace MuAux

/-- An **entrywise functor** `𝒦 ⊗ -`: `⋆`-homomorphisms `f : X → Y` induce `S.map f : 𝒦 ⊗ X →
𝒦 ⊗ Y` with `S.map f (e_{ij} ⊗ x) = e_{ij} ⊗ f x`. -/
structure StabFunctor where
  /-- The induced map `id_𝒦 ⊗ f`. -/
  map : ∀ {X Y : Type u} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y],
    (X →⋆ₙₐ[ℂ] Y) → (Stab X →⋆ₙₐ[ℂ] Stab Y)
  /-- `S.map f` acts entrywise on the matrix units. -/
  map_single : ∀ {X Y : Type u} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (f : X →⋆ₙₐ[ℂ] Y) (i j : ℕ) (x : X), map f (Stab.single i j x) = Stab.single i j (f x)

/-- The inclusion `qB ↪ B * B`. -/
def jq (B : Type u) [NonUnitalCStarAlgebra B] : Qalg B →⋆ₙₐ[ℂ] FreeUnital B :=
  NonUnitalStarSubalgebraClass.subtype (Qalg.ideal B)

theorem jq_injective (B : Type u) [NonUnitalCStarAlgebra B] : Function.Injective (jq B) :=
  fun _ _ h => Subtype.ext h

section Unitization

variable {E : Type*} [NonUnitalCStarAlgebra E]

theorem mul_inr_eq (d : Unitization ℂ E) (z : E) :
    d * (z : Unitization ℂ E) = ((d.fst • z + d.snd * z : E) : Unitization ℂ E) := by
  refine Unitization.ext ?_ ?_
  · rw [Unitization.fst_mul, Unitization.fst_inr ℂ z, mul_zero, Unitization.fst_inr]
  · rw [Unitization.snd_mul, Unitization.snd_inr ℂ z, Unitization.fst_inr ℂ z, zero_smul ℂ,
      add_zero, Unitization.snd_inr]

theorem inr_mul_eq (d : Unitization ℂ E) (z : E) :
    (z : Unitization ℂ E) * d = ((d.fst • z + z * d.snd : E) : Unitization ℂ E) := by
  refine Unitization.ext ?_ ?_
  · rw [Unitization.fst_mul, Unitization.fst_inr ℂ z, zero_mul, Unitization.fst_inr]
  · rw [Unitization.snd_mul, Unitization.snd_inr ℂ z, Unitization.fst_inr ℂ z, zero_smul ℂ,
      zero_add, Unitization.snd_inr]

end Unitization

namespace StabFunctor

variable (S : StabFunctor.{u})

theorem map_comp {X Y Z : Type u} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    [NonUnitalCStarAlgebra Z] (g : Y →⋆ₙₐ[ℂ] Z) (f : X →⋆ₙₐ[ℂ] Y) :
    S.map (g.comp f) = (S.map g).comp (S.map f) :=
  hom_ext_single fun i j b => (S.map_single (g.comp f) i j b).trans
    ((S.map_single g i j (f b)).symm.trans (congrArg (S.map g) (S.map_single f i j b).symm))

theorem map_zero_hom {X Y : Type u} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y] :
    S.map (0 : X →⋆ₙₐ[ℂ] Y) = 0 :=
  hom_ext_single fun i j b => (S.map_single (0 : X →⋆ₙₐ[ℂ] Y) i j b).trans
    ((congrArg (Stab.single i j) (NonUnitalStarAlgHom.zero_apply (R := ℂ) (B := Y) b)).trans
      ((Stab.single_zero i j).trans
        (NonUnitalStarAlgHom.zero_apply (R := ℂ) (B := Stab Y) (Stab.single i j b)).symm))

variable (B : Type u) [NonUnitalCStarAlgebra B]

theorem mapJq_injective : Function.Injective (S.map (jq B)) :=
  injective_of_single (jq B) (jq_injective B) (S.map (jq B)) (S.map_single (jq B))

/-- The embedding `𝒦 ⊗ qB ↪ (𝒦 ⊗ (B * B))^+`. -/
def emb : Stab (Qalg B) →⋆ₙₐ[ℂ] Unitization ℂ (Stab (FreeUnital B)) :=
  (Unitization.inrNonUnitalStarAlgHom ℂ (Stab (FreeUnital B))).comp (S.map (jq B))

theorem emb_apply (x : Stab (Qalg B)) :
    S.emb B x = ((S.map (jq B) x : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
  rfl

theorem emb_injective : Function.Injective (S.emb B) := by
  intro x y h
  have h' : ((S.map (jq B) x : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) =
      S.map (jq B) y := h
  exact S.mapJq_injective B (Unitization.inr_injective h')

/-- The closed ideal `𝒦 ⊗ qB` of `(𝒦 ⊗ (B * B))^+`, as the range of `emb`. -/
abbrev J : NonUnitalStarSubalgebra ℂ (Unitization ℂ (Stab (FreeUnital B))) :=
  NonUnitalStarAlgHom.range (S.emb B)

theorem isClosed_J : IsClosed (S.J B : Set (Unitization ℂ (Stab (FreeUnital B)))) :=
  isClosed_range_hom (S.emb B) (S.emb_injective B)

/-- `𝒦 ⊗ qB` is a two-sided ideal of `(𝒦 ⊗ (B * B))^+`. -/
theorem J_ideal (d x : Unitization ℂ (Stab (FreeUnital B))) (hx : x ∈ S.J B) :
    d * x ∈ S.J B ∧ x * d ∈ S.J B := by
  obtain ⟨w, rfl⟩ := (NonUnitalStarAlgHom.mem_range (S.emb B)).mp hx
  have hG := mul_mem_range (jq B) (S.map (jq B)) (S.map_single (jq B))
    (isClosed_range_hom _ (S.mapJq_injective B))
    (fun a b => ⟨⟨a * (b : FreeUnital B), Qalg.mul_mem_left b.2 a⟩, rfl⟩)
    (fun a b => ⟨⟨(b : FreeUnital B) * a, Qalg.mul_mem_right b.2 a⟩, rfl⟩) d.snd w
  obtain ⟨w₁, hw₁⟩ := hG.1
  obtain ⟨w₂, hw₂⟩ := hG.2
  refine ⟨(NonUnitalStarAlgHom.mem_range (S.emb B)).mpr ⟨d.fst • w + w₁, ?_⟩,
    (NonUnitalStarAlgHom.mem_range (S.emb B)).mpr ⟨d.fst • w + w₂, ?_⟩⟩
  · rw [S.emb_apply, S.emb_apply, mul_inr_eq, map_add, map_smul, hw₁]
  · rw [S.emb_apply, S.emb_apply, inr_mul_eq, map_add, map_smul, hw₂]

/-- `𝒦 ⊗ B → (𝒦 ⊗ (B * B))^+` induced by the first inclusion `ι`. -/
def emb₁ : Stab B →⋆ₙₐ[ℂ] Unitization ℂ (Stab (FreeUnital B)) :=
  (Unitization.inrNonUnitalStarAlgHom ℂ (Stab (FreeUnital B))).comp (S.map (ι₁ B))

/-- `𝒦 ⊗ B → (𝒦 ⊗ (B * B))^+` induced by the second inclusion `ῑ`. -/
def emb₂ : Stab B →⋆ₙₐ[ℂ] Unitization ℂ (Stab (FreeUnital B)) :=
  (Unitization.inrNonUnitalStarAlgHom ℂ (Stab (FreeUnital B))).comp (S.map (ι₂ B))

/-- `(S.map ι, S.map ῑ)` is a quasihomomorphism into `𝒦 ⊗ qB`. -/
theorem sub_mem_J (a : Stab B) : S.emb₁ B a - S.emb₂ B a ∈ S.J B := by
  refine induction_single ?_ ?_ ?_ a
  · have hc : Continuous fun x => S.emb₁ B x - S.emb₂ B x :=
      (continuous_hom (S.emb₁ B)).sub (continuous_hom (S.emb₂ B))
    exact (S.isClosed_J B).preimage hc
  · intro i j b
    refine (NonUnitalStarAlgHom.mem_range (S.emb B)).mpr ⟨Stab.single i j (Qalg.q B b), ?_⟩
    show ((S.map (jq B) (Stab.single i j (Qalg.q B b)) : Stab (FreeUnital B)) :
        Unitization ℂ (Stab (FreeUnital B))) =
      ((S.map (ι₁ B) (Stab.single i j b) : Stab (FreeUnital B)) :
        Unitization ℂ (Stab (FreeUnital B))) -
      ((S.map (ι₂ B) (Stab.single i j b) : Stab (FreeUnital B)) :
        Unitization ℂ (Stab (FreeUnital B)))
    rw [S.map_single, S.map_single, S.map_single, ← Unitization.inr_sub]
    exact congrArg (fun z : Stab (FreeUnital B) => (z : Unitization ℂ (Stab (FreeUnital B))))
      (map_sub (Stab.singleₗ i j) (ι₁ B b) (ι₂ B b))
  · intro x y hx hy
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hx hy

/-- The unital `⋆`-homomorphism `(𝒦 ⊗ B) * (𝒦 ⊗ B) → (𝒦 ⊗ (B * B))^+` of the pair
`(S.map ι, S.map ῑ)`. -/
def pre : FreeUnital (Stab B) →⋆ₐ[ℂ] Unitization ℂ (Stab (FreeUnital B)) :=
  FreeProd.lift _ (S.emb₁ B) (S.emb₂ B)

theorem pre_ι₁ (a : Stab B) :
    S.pre B (ι₁ (Stab B) a) =
      ((S.map (ι₁ B) a : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
  FreeProd.lift_ι₁ _ (S.emb₁ B) (S.emb₂ B) a

theorem pre_ι₂ (a : Stab B) :
    S.pre B (ι₂ (Stab B) a) =
      ((S.map (ι₂ B) a : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
  FreeProd.lift_ι₂ _ (S.emb₁ B) (S.emb₂ B) a

/-- The lift `q(𝒦 ⊗ B) → 𝒦 ⊗ qB` (as the ideal `J`) of the quasihomomorphism. -/
def liftJ : Qalg (Stab B) →⋆ₙₐ[ℂ] S.J B :=
  Qalg.lift (S.emb₁ B) (S.emb₂ B) (S.J B) (S.isClosed_J B) (S.J_ideal B) (S.sub_mem_J B)

/-- `𝒦 ⊗ qB ≅ J`. -/
def equivJ : Stab (Qalg B) ≃⋆ₐ[ℂ] S.J B :=
  StarAlgEquiv.ofInjective' (S.emb B) (S.emb_injective B)

/-- **Cuntz's comparison map** `μ : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`,
`μ (q (e_{ij} ⊗ b)) = e_{ij} ⊗ q b`. -/
def mu : Qalg (Stab B) →⋆ₙₐ[ℂ] Stab (Qalg B) :=
  (S.equivJ B).symm.toNonUnitalStarAlgHom.comp (S.liftJ B)

theorem coe_equivJ (y : Stab (Qalg B)) :
    ((S.equivJ B y : S.J B) : Unitization ℂ (Stab (FreeUnital B))) = S.emb B y :=
  rfl

theorem coe_liftJ (x : Qalg (Stab B)) :
    ((S.liftJ B x : S.J B) : Unitization ℂ (Stab (FreeUnital B))) =
      S.pre B (x : FreeUnital (Stab B)) :=
  rfl

/-- **Characterization of `μ`**: `emb ∘ μ` is the restriction of `S.map ι * S.map ῑ` to
`q(𝒦 ⊗ B)`. -/
theorem emb_mu (x : Qalg (Stab B)) :
    S.emb B (S.mu B x) = S.pre B (x : FreeUnital (Stab B)) :=
  ((S.coe_equivJ B ((S.equivJ B).symm (S.liftJ B x))).symm.trans
    (congrArg Subtype.val ((S.equivJ B).apply_symm_apply (S.liftJ B x)))).trans
    (S.coe_liftJ B x)

end StabFunctor

end MuAux

end

end GroupApproximation.Full.TWWKK
