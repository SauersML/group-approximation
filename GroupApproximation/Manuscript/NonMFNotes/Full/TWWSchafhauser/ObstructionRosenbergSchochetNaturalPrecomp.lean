import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetTransfer
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetComap
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnital

/-!
# Naturality of boundary maps: the formal part

Lane `TWWSch3d3-3B`, work order `WO-TWWSchafhauser-3d3-3B` (Rosenberg–Schochet injectivity
half). Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378),
through C. Schafhauser, J. reine angew. Math. 759 (2020), §§4--5.

The boundary maps of an extension class `ξ ∈ Ext(S, J)` are homomorphisms
`K₀(S) → K₁(J)` and `K₁(S) → K₀(J)` (B. Blackadar, *K-theory for operator algebras*, 17.1.2,
19.5.7; M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*,
9.1.5, 12.2.2). They are natural in `S`: pulling `ξ` back along `φ : A → B` precomposes them
with `φ_*` (J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), §1). This file contains the
purely algebraic parts of that statement.

* `precompHom f : (N →+ P) →+ (M →+ P)`, `g ↦ g ∘ f`;
* `ExtGroup.natural_of_mk`: a naturality identity `β_A (φ^* ξ) = β_B ξ ∘ m` holds on all of
  `Ext(B, J)` once it holds on the classes of Busby cycles;
* `ExtKKAction.preservesNull_of_precomp`: boundary maps valued in `Hom(K_*(-), K_{*+1}J)` which
  intertwine a `KK`-action with precomposition by `K`-theory maps preserve "both boundaries
  vanish". This specialises `ExtKKAction.preservesNull_of_boundaries`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

section Precomp

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- **Precomposition** with `f : M →+ N`, as an additive map `(N →+ P) →+ (M →+ P)`. -/
def precompHom (f : M →+ N) : (N →+ P) →+ (M →+ P) where
  toFun g := g.comp f
  map_zero' := AddMonoidHom.ext fun _ => rfl
  map_add' _ _ := AddMonoidHom.ext fun _ => rfl

theorem precompHom_apply (f : M →+ N) (g : N →+ P) : precompHom f g = g.comp f :=
  rfl

end Precomp

section NaturalOfMk

variable {A B : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
variable {MA MB N : Type*} [AddCommGroup MA] [AddCommGroup MB] [AddCommGroup N]

/-- **Naturality from cycles.** Let `β_A : Ext(A, J) → Hom(M_A, N)` and
`β_B : Ext(B, J) → Hom(M_B, N)` be additive and `m : M_A → M_B`. If
`β_A [x ∘ φ] = β_B [x] ∘ m` for every Busby cycle `x`, then `β_A (φ^* ξ) = β_B ξ ∘ m` for every
`ξ ∈ Ext(B, J)`. -/
theorem ExtGroup.natural_of_mk (φ : A →⋆ₙₐ[ℂ] B) (βA : ExtGroup A J →+ (MA →+ N))
    (βB : ExtGroup B J →+ (MB →+ N)) (m : MA →+ MB)
    (h : ∀ x : BusbyCycle B J, βA (ExtGroup.mk (x.comap φ)) = (βB (ExtGroup.mk x)).comp m)
    (ξ : ExtGroup B J) : βA (ExtGroup.comap φ ξ) = (βB ξ).comp m := by
  have key : (βA.comp (ExtGroup.comap φ) : ExtGroup B J →+ (MA →+ N)) =
      (precompHom m).comp βB := by
    refine ExtGroup.hom_ext fun x => ?_
    calc (βA.comp (ExtGroup.comap φ)) (ExtGroup.mk x)
        = βA (ExtGroup.comap φ (ExtGroup.mk x)) := rfl
      _ = βA (ExtGroup.mk (x.comap φ)) := by rw [ExtGroup.comap_mk]
      _ = (βB (ExtGroup.mk x)).comp m := h x
      _ = ((precompHom m).comp βB) (ExtGroup.mk x) := rfl
  calc βA (ExtGroup.comap φ ξ) = (βA.comp (ExtGroup.comap φ)) ξ := rfl
    _ = ((precompHom m).comp βB) ξ := by rw [key]
    _ = (βB ξ).comp m := rfl

end NaturalOfMk

section PreservesNull

variable {T : KasparovTheory.{0}} {P : SepCStarAlgebra.{0} → Prop}
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Boundary maps natural for a `KK`-action preserve vanishing.** Let
`β₀ A : Ext(A, J) → Hom(K₀A, K₁J)` and `β₁ A : Ext(A, J) → Hom(K₁A, K₀J)` be additive, and let
`k₀ x : K₀A → K₀B`, `k₁ x : K₁A → K₁B` be the `K`-theory maps of `x ∈ KK(A, B)`. If
`β_i A (x^* ξ) = β_i B ξ ∘ k_i x`, then "both boundaries of `ξ` vanish" is preserved by the
action. -/
theorem ExtKKAction.preservesNull_of_precomp (Φ : ExtKKAction T P J)
    (β₀ : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J →+ (KZeroN A →+ KOneN J))
    (β₁ : ∀ A : SepCStarAlgebra.{0}, ExtGroup A J →+ (KOneN A →+ KZeroN J))
    (k₀ : ∀ {A B : SepCStarAlgebra.{0}}, P A → P B → T.Grp A B → (KZeroN A →+ KZeroN B))
    (k₁ : ∀ {A B : SepCStarAlgebra.{0}}, P A → P B → T.Grp A B → (KOneN A →+ KOneN B))
    (nat₀ : ∀ {A B : SepCStarAlgebra.{0}} (hA : P A) (hB : P B) (x : T.Grp A B)
      (ξ : ExtGroup B J), β₀ A (Φ.act hA hB x ξ) = (β₀ B ξ).comp (k₀ hA hB x))
    (nat₁ : ∀ {A B : SepCStarAlgebra.{0}} (hA : P A) (hB : P B) (x : T.Grp A B)
      (ξ : ExtGroup B J), β₁ A (Φ.act hA hB x ξ) = (β₁ B ξ).comp (k₁ hA hB x)) :
    Φ.PreservesNull (fun A ξ => β₀ A ξ = 0 ∧ β₁ A ξ = 0) := by
  intro A B hA hB x ξ hξ
  have h0 : β₀ B ξ = 0 := hξ.1
  have h1 : β₁ B ξ = 0 := hξ.2
  refine ⟨?_, ?_⟩
  · show β₀ A (Φ.act hA hB x ξ) = 0
    exact (nat₀ hA hB x ξ).trans
      ((congrArg (fun g => AddMonoidHom.comp g (k₀ hA hB x)) h0).trans
        (AddMonoidHom.zero_comp _))
  · show β₁ A (Φ.act hA hB x ξ) = 0
    exact (nat₁ hA hB x ξ).trans
      ((congrArg (fun g => AddMonoidHom.comp g (k₁ hA hB x)) h1).trans
        (AddMonoidHom.zero_comp _))

end PreservesNull

end GroupApproximation.Full.TWWSchafhauser
