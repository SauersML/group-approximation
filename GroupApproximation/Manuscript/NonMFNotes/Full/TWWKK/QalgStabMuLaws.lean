import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgStabMuCore

/-!
# Laws of Cuntz's comparison map `μ : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`

For an abstract entrywise functor `S` (`QalgStabMuCore`):

* `map_pi_comp_mu`: `(id_𝒦 ⊗ π_B) ∘ μ_B = π_{𝒦 ⊗ B}`;
* `mu_comp_map_map`: naturality, `μ_C ∘ q(id_𝒦 ⊗ f) = (id_𝒦 ⊗ q f) ∘ μ_B`.

Both are proved by embedding into unitizations and using the uniqueness part of the universal
property of the full free product (`FreeProd.hom_ext`).

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

/-- `π̃ : A * A → Ã` as a non-unital `⋆`-homomorphism. -/
abbrev piPreNU (A : Type u) [NonUnitalCStarAlgebra A] : FreeUnital A →⋆ₙₐ[ℂ] Unitization ℂ A :=
  (Qalg.piPre A).toNonUnitalStarAlgHom

/-- The inclusion `A ↪ Ã`. -/
abbrev inrNU (A : Type u) [NonUnitalCStarAlgebra A] : A →⋆ₙₐ[ℂ] Unitization ℂ A :=
  Unitization.inrNonUnitalStarAlgHom ℂ A

theorem piPre_eq_inr {A : Type u} [NonUnitalCStarAlgebra A] (x : Qalg A) :
    Qalg.piPre A (x : FreeUnital A) = ((Qalg.pi A x : A) : Unitization ℂ A) :=
  Unitization.ext ((Qalg.fst_piPre_of_mem x.2).trans (Unitization.fst_inr ℂ _).symm) rfl

theorem inr_comp_pi (A : Type u) [NonUnitalCStarAlgebra A] :
    (inrNU A).comp (Qalg.pi A) = (piPreNU A).comp (jq A) :=
  NonUnitalStarAlgHom.ext fun x => (piPre_eq_inr x).symm

theorem piPre_comp_ι₁ (A : Type u) [NonUnitalCStarAlgebra A] :
    (piPreNU A).comp (ι₁ A) = inrNU A :=
  NonUnitalStarAlgHom.ext fun a => Qalg.piPre_ι₁ a

theorem piPre_comp_ι₂ (A : Type u) [NonUnitalCStarAlgebra A] : (piPreNU A).comp (ι₂ A) = 0 :=
  NonUnitalStarAlgHom.ext fun a =>
    (Qalg.piPre_ι₂ a).trans (NonUnitalStarAlgHom.zero_apply (R := ℂ) a).symm

section Nat

variable {B C : Type u} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

theorem jq_comp_map (f : B →⋆ₙₐ[ℂ] C) :
    (FreeProd.freeMap f).toNonUnitalStarAlgHom.comp (jq B) = (jq C).comp (Qalg.map f) :=
  NonUnitalStarAlgHom.ext fun _ => rfl

theorem freeMap_comp_ι₁ (f : B →⋆ₙₐ[ℂ] C) :
    (FreeProd.freeMap f).toNonUnitalStarAlgHom.comp (ι₁ B) = (ι₁ C).comp f :=
  NonUnitalStarAlgHom.ext fun a => FreeProd.freeMap_ι₁ f a

theorem freeMap_comp_ι₂ (f : B →⋆ₙₐ[ℂ] C) :
    (FreeProd.freeMap f).toNonUnitalStarAlgHom.comp (ι₂ B) = (ι₂ C).comp f :=
  NonUnitalStarAlgHom.ext fun a => FreeProd.freeMap_ι₂ f a

end Nat

namespace StabFunctor

variable (S : StabFunctor.{u})

section Pi

variable (B : Type u) [NonUnitalCStarAlgebra B]

theorem map_piPre_ι₁ : (S.map (piPreNU B)).comp (S.map (ι₁ B)) = S.map (inrNU B) := by
  rw [← S.map_comp, piPre_comp_ι₁]

theorem map_piPre_ι₂ : (S.map (piPreNU B)).comp (S.map (ι₂ B)) = 0 := by
  rw [← S.map_comp, piPre_comp_ι₂, S.map_zero_hom]

theorem map_inr_pi :
    (S.map (inrNU B)).comp (S.map (Qalg.pi B)) = (S.map (piPreNU B)).comp (S.map (jq B)) := by
  rw [← S.map_comp, ← S.map_comp, inr_comp_pi]

theorem mapInr_injective : Function.Injective (S.map (inrNU B)) :=
  injective_of_single (inrNU B)
    (fun a b h => Unitization.inr_injective (R := ℂ) (h : (a : Unitization ℂ B) = b))
    (S.map (inrNU B)) (S.map_single (inrNU B))

theorem starMap_comp_pre :
    (Unitization.starMap (S.map (piPreNU B))).comp (S.pre B) =
      (Unitization.starMap (S.map (inrNU B))).comp (Qalg.piPre (Stab B)) := by
  refine FreeProd.hom_ext (fun a => ?_) (fun a => ?_)
  · calc Unitization.starMap (S.map (piPreNU B)) (S.pre B (ι₁ (Stab B) a))
        = Unitization.starMap (S.map (piPreNU B))
            ((S.map (ι₁ B) a : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
          congrArg (Unitization.starMap (S.map (piPreNU B))) (S.pre_ι₁ B a)
      _ = ((S.map (piPreNU B) (S.map (ι₁ B) a) : Stab (Unitization ℂ B)) :
            Unitization ℂ (Stab (Unitization ℂ B))) :=
          Unitization.starMap_inr (S.map (piPreNU B)) (S.map (ι₁ B) a)
      _ = ((S.map (inrNU B) a : Stab (Unitization ℂ B)) :
            Unitization ℂ (Stab (Unitization ℂ B))) :=
          congrArg (fun z : Stab (Unitization ℂ B) => (z : Unitization ℂ (Stab (Unitization ℂ B))))
            (DFunLike.congr_fun (S.map_piPre_ι₁ B) a)
      _ = Unitization.starMap (S.map (inrNU B)) ((a : Stab B) : Unitization ℂ (Stab B)) :=
          (Unitization.starMap_inr (S.map (inrNU B)) a).symm
      _ = Unitization.starMap (S.map (inrNU B)) (Qalg.piPre (Stab B) (ι₁ (Stab B) a)) :=
          congrArg (Unitization.starMap (S.map (inrNU B))) (Qalg.piPre_ι₁ a).symm
  · calc Unitization.starMap (S.map (piPreNU B)) (S.pre B (ι₂ (Stab B) a))
        = Unitization.starMap (S.map (piPreNU B))
            ((S.map (ι₂ B) a : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
          congrArg (Unitization.starMap (S.map (piPreNU B))) (S.pre_ι₂ B a)
      _ = ((S.map (piPreNU B) (S.map (ι₂ B) a) : Stab (Unitization ℂ B)) :
            Unitization ℂ (Stab (Unitization ℂ B))) :=
          Unitization.starMap_inr (S.map (piPreNU B)) (S.map (ι₂ B) a)
      _ = (((0 : Stab (Unitization ℂ B)) : Stab (Unitization ℂ B)) :
            Unitization ℂ (Stab (Unitization ℂ B))) :=
          congrArg (fun z : Stab (Unitization ℂ B) => (z : Unitization ℂ (Stab (Unitization ℂ B))))
            ((DFunLike.congr_fun (S.map_piPre_ι₂ B) a).trans
              (NonUnitalStarAlgHom.zero_apply (R := ℂ) (B := Stab (Unitization ℂ B)) a))
      _ = 0 := Unitization.inr_zero ℂ
      _ = Unitization.starMap (S.map (inrNU B)) 0 :=
          (map_zero (Unitization.starMap (S.map (inrNU B)))).symm
      _ = Unitization.starMap (S.map (inrNU B)) (Qalg.piPre (Stab B) (ι₂ (Stab B) a)) :=
          congrArg (Unitization.starMap (S.map (inrNU B))) (Qalg.piPre_ι₂ a).symm

/-- **Compatibility of `μ` with `π`**: `(id_𝒦 ⊗ π_B) ∘ μ_B = π_{𝒦 ⊗ B}`. -/
theorem map_pi_comp_mu : (S.map (Qalg.pi B)).comp (S.mu B) = Qalg.pi (Stab B) := by
  refine NonUnitalStarAlgHom.ext fun x =>
    S.mapInr_injective B (Unitization.inr_injective (R := ℂ) ?_)
  calc ((S.map (inrNU B) (S.map (Qalg.pi B) (S.mu B x)) : Stab (Unitization ℂ B)) :
        Unitization ℂ (Stab (Unitization ℂ B)))
      = ((S.map (piPreNU B) (S.map (jq B) (S.mu B x)) : Stab (Unitization ℂ B)) :
          Unitization ℂ (Stab (Unitization ℂ B))) :=
        congrArg (fun z : Stab (Unitization ℂ B) => (z : Unitization ℂ (Stab (Unitization ℂ B))))
          (DFunLike.congr_fun (S.map_inr_pi B) (S.mu B x))
    _ = Unitization.starMap (S.map (piPreNU B)) (S.emb B (S.mu B x)) :=
        (Unitization.starMap_inr (S.map (piPreNU B)) (S.map (jq B) (S.mu B x))).symm
    _ = Unitization.starMap (S.map (piPreNU B)) (S.pre B (x : FreeUnital (Stab B))) :=
        congrArg (Unitization.starMap (S.map (piPreNU B))) (S.emb_mu B x)
    _ = Unitization.starMap (S.map (inrNU B)) (Qalg.piPre (Stab B) (x : FreeUnital (Stab B))) :=
        DFunLike.congr_fun (S.starMap_comp_pre B) (x : FreeUnital (Stab B))
    _ = Unitization.starMap (S.map (inrNU B))
          ((Qalg.pi (Stab B) x : Stab B) : Unitization ℂ (Stab B)) :=
        congrArg (Unitization.starMap (S.map (inrNU B))) (piPre_eq_inr x)
    _ = ((S.map (inrNU B) (Qalg.pi (Stab B) x) : Stab (Unitization ℂ B)) :
          Unitization ℂ (Stab (Unitization ℂ B))) :=
        Unitization.starMap_inr (S.map (inrNU B)) (Qalg.pi (Stab B) x)

end Pi

section Nat

variable {B C : Type u} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

theorem map_jq_nat (f : B →⋆ₙₐ[ℂ] C) :
    (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom).comp (S.map (jq B)) =
      (S.map (jq C)).comp (S.map (Qalg.map f)) := by
  rw [← S.map_comp, ← S.map_comp, jq_comp_map]

theorem map_ι₁_nat (f : B →⋆ₙₐ[ℂ] C) :
    (S.map (ι₁ C)).comp (S.map f) =
      (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom).comp (S.map (ι₁ B)) := by
  rw [← S.map_comp, ← S.map_comp, freeMap_comp_ι₁]

theorem map_ι₂_nat (f : B →⋆ₙₐ[ℂ] C) :
    (S.map (ι₂ C)).comp (S.map f) =
      (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom).comp (S.map (ι₂ B)) := by
  rw [← S.map_comp, ← S.map_comp, freeMap_comp_ι₂]

theorem pre_comp_freeMap (f : B →⋆ₙₐ[ℂ] C) :
    (S.pre C).comp (FreeProd.freeMap (S.map f)) =
      (Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)).comp (S.pre B) := by
  refine FreeProd.hom_ext (fun a => ?_) (fun a => ?_)
  · calc S.pre C (FreeProd.freeMap (S.map f) (ι₁ (Stab B) a))
        = S.pre C (ι₁ (Stab C) (S.map f a)) :=
          congrArg (S.pre C) (FreeProd.freeMap_ι₁ (S.map f) a)
      _ = ((S.map (ι₁ C) (S.map f a) : Stab (FreeUnital C)) :
            Unitization ℂ (Stab (FreeUnital C))) := S.pre_ι₁ C (S.map f a)
      _ = ((S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom (S.map (ι₁ B) a) :
            Stab (FreeUnital C)) : Unitization ℂ (Stab (FreeUnital C))) :=
          congrArg (fun z : Stab (FreeUnital C) => (z : Unitization ℂ (Stab (FreeUnital C))))
            (DFunLike.congr_fun (S.map_ι₁_nat f) a)
      _ = Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
            ((S.map (ι₁ B) a : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
          (Unitization.starMap_inr (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
            (S.map (ι₁ B) a)).symm
      _ = Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
            (S.pre B (ι₁ (Stab B) a)) :=
          congrArg (Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom))
            (S.pre_ι₁ B a).symm
  · calc S.pre C (FreeProd.freeMap (S.map f) (ι₂ (Stab B) a))
        = S.pre C (ι₂ (Stab C) (S.map f a)) :=
          congrArg (S.pre C) (FreeProd.freeMap_ι₂ (S.map f) a)
      _ = ((S.map (ι₂ C) (S.map f a) : Stab (FreeUnital C)) :
            Unitization ℂ (Stab (FreeUnital C))) := S.pre_ι₂ C (S.map f a)
      _ = ((S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom (S.map (ι₂ B) a) :
            Stab (FreeUnital C)) : Unitization ℂ (Stab (FreeUnital C))) :=
          congrArg (fun z : Stab (FreeUnital C) => (z : Unitization ℂ (Stab (FreeUnital C))))
            (DFunLike.congr_fun (S.map_ι₂_nat f) a)
      _ = Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
            ((S.map (ι₂ B) a : Stab (FreeUnital B)) : Unitization ℂ (Stab (FreeUnital B))) :=
          (Unitization.starMap_inr (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
            (S.map (ι₂ B) a)).symm
      _ = Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
            (S.pre B (ι₂ (Stab B) a)) :=
          congrArg (Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom))
            (S.pre_ι₂ B a).symm

/-- **Naturality of `μ`**: `μ_C ∘ q(id_𝒦 ⊗ f) = (id_𝒦 ⊗ q f) ∘ μ_B`. -/
theorem mu_comp_map_map (f : B →⋆ₙₐ[ℂ] C) :
    (S.mu C).comp (Qalg.map (S.map f)) = (S.map (Qalg.map f)).comp (S.mu B) := by
  refine NonUnitalStarAlgHom.ext fun x => S.emb_injective C ?_
  calc S.emb C (S.mu C (Qalg.map (S.map f) x))
      = S.pre C (FreeProd.freeMap (S.map f) (x : FreeUnital (Stab B))) :=
        S.emb_mu C (Qalg.map (S.map f) x)
    _ = Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
          (S.pre B (x : FreeUnital (Stab B))) :=
        DFunLike.congr_fun (S.pre_comp_freeMap f) (x : FreeUnital (Stab B))
    _ = Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
          (S.emb B (S.mu B x)) :=
        congrArg (Unitization.starMap (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom))
          (S.emb_mu B x).symm
    _ = ((S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom (S.map (jq B) (S.mu B x)) :
          Stab (FreeUnital C)) : Unitization ℂ (Stab (FreeUnital C))) :=
        Unitization.starMap_inr (S.map (FreeProd.freeMap f).toNonUnitalStarAlgHom)
          (S.map (jq B) (S.mu B x))
    _ = ((S.map (jq C) (S.map (Qalg.map f) (S.mu B x)) : Stab (FreeUnital C)) :
          Unitization ℂ (Stab (FreeUnital C))) :=
        congrArg (fun z : Stab (FreeUnital C) => (z : Unitization ℂ (Stab (FreeUnital C))))
          (DFunLike.congr_fun (S.map_jq_nat f) (S.mu B x))
    _ = S.emb C (S.map (Qalg.map f) (S.mu B x)) := rfl

end Nat

end StabFunctor

end MuAux

end

end GroupApproximation.Full.TWWKK
