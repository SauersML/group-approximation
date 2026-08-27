import GroupApproximation.Higman.HNNSubextensionFiniteBaseProfinite
import GroupApproximation.Higman.FreeLampFinitePresentation

/-!
# Finite-base free lamps are subgroup separable

For `G *_M (M × F(α))`, the base translates a `G`-state and a lamp
letter writes the pair consisting of its current right `M`-coset and its
generator.  This is the multi-stable-letter version of the faithful
free-label action for a central HNN extension.
-/

namespace GroupApproximation
namespace Higman
namespace FreeLampFiniteBaseProfinite

noncomputable section

open Monoid

variable {G α : Type} [Group G] (M : Subgroup G)

/-- The right-coset labels supplied by the central-HNN transversal. -/
abbrev Label
    (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  CentralHNNFreeLabel.Label M d

/-- A free-lamp label remembers both the current edge coset and the lamp
generator being read. -/
abbrev LampLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  Label M d × α

/-- State space of the free-label action. -/
abbrev Space
    (d : HNNExtension.NormalWord.TransversalPair G M M) :=
  G × FreeGroup (LampLabel (M := M) (α := α) d)

/-- The chosen label of the right `M`-coset containing `x`. -/
def cosetLabel
    (d : HNNExtension.NormalWord.TransversalPair G M M) (x : G) : Label M d :=
  ((d.compl (1 : ℤˣ)).equiv x).2

/-- Base elements act by left translation on the base state. -/
def basePerm
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    Equiv.Perm (Space (M := M) (α := α) d) :=
  Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)

@[simp] theorem basePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g x : G) (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    basePerm (M := M) (α := α) d g (x, w) = (g * x, w) := rfl

/-- A lamp word writes a copy of itself tagged by the current edge coset. -/
def lampPerm
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (k : FreeGroup α) : Equiv.Perm (Space (M := M) (α := α) d) where
  toFun p :=
    (p.1, FreeGroup.map (fun i ↦ (cosetLabel M d p.1, i)) k * p.2)
  invFun p :=
    (p.1, (FreeGroup.map (fun i ↦ (cosetLabel M d p.1, i)) k)⁻¹ * p.2)
  left_inv p := by rcases p with ⟨x, w⟩; apply Prod.ext <;> simp
  right_inv p := by rcases p with ⟨x, w⟩; apply Prod.ext <;> simp

@[simp] theorem lampPerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (k : FreeGroup α) (x : G)
    (w : FreeGroup (LampLabel (M := M) (α := α) d)) :
    lampPerm (M := M) d k (x, w) =
      (x, FreeGroup.map (fun i ↦ (cosetLabel M d x, i)) k * w) := rfl

/-- The base action as a homomorphism. -/
def basePermHom
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    G →* Equiv.Perm (Space (M := M) (α := α) d) where
  toFun := basePerm (M := M) (α := α) d
  map_one' := by ext p <;> simp [basePerm]
  map_mul' g h := by ext p <;> simp [basePerm, mul_assoc]

/-- Lamp words act homomorphically because they leave the base state fixed. -/
def lampPermHom
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup α →* Equiv.Perm (Space (M := M) (α := α) d) where
  toFun := lampPerm (M := M) d
  map_one' := by
    ext p <;> rcases p with ⟨x, w⟩ <;> simp [lampPerm]
  map_mul' k l := by
    ext p <;> rcases p with ⟨x, w⟩
    · rfl
    · simp only [lampPerm_apply, Equiv.Perm.mul_apply, map_mul]
      group

/-- Left multiplication by an edge element does not change the coset label. -/
theorem cosetLabel_mul_left
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (m : M) (x : G) :
    cosetLabel M d ((m : G) * x) = cosetLabel M d x := by
  exact CentralHNNFreeLabel.label_mul_left M d m x

/-- Edge translations commute with every lamp word. -/
theorem edge_commutes_lamp
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (m : M) (k : FreeGroup α) :
    Commute
      (basePerm (M := M) (α := α) d (m : G))
      (lampPerm (M := M) d k) := by
  apply Equiv.Perm.ext
  rintro ⟨x, w⟩
  apply Prod.ext
  · rfl
  · simp only [Equiv.Perm.mul_apply, basePerm_apply, lampPerm_apply]
    rw [cosetLabel_mul_left]

/-- Action of the lamp-augmented edge factor. -/
def lampFactorPerm
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    M × FreeGroup α →* Equiv.Perm (Space (M := M) (α := α) d) where
  toFun p :=
    basePerm (M := M) (α := α) d (p.1 : G) * lampPerm (M := M) d p.2
  map_one' := by ext p <;> rcases p with ⟨x, w⟩ <;> simp
  map_mul' p q := by
    change basePerm (M := M) (α := α) d ((p.1 * q.1 : M) : G) *
        lampPerm (M := M) d (p.2 * q.2) = _
    rw [show basePerm (M := M) (α := α) d ((p.1 * q.1 : M) : G) =
        basePerm (M := M) (α := α) d (p.1 : G) *
          basePerm (M := M) (α := α) d (q.1 : G) by
          apply Equiv.Perm.ext
          rintro ⟨x, w⟩
          apply Prod.ext <;> simp [basePerm, mul_assoc],
      show lampPerm (M := M) d (p.2 * q.2) =
        lampPerm (M := M) d p.2 * lampPerm (M := M) d q.2 by
          exact map_mul (lampPermHom (M := M) d) p.2 q.2]
    calc
      basePerm (M := M) (α := α) d (p.1 : G) *
            basePerm (M := M) (α := α) d (q.1 : G) *
          (lampPerm (M := M) d p.2 * lampPerm (M := M) d q.2) =
          basePerm (M := M) (α := α) d (p.1 : G) *
            (basePerm (M := M) (α := α) d (q.1 : G) *
              lampPerm (M := M) d p.2) * lampPerm (M := M) d q.2 := by group
      _ = basePerm (M := M) (α := α) d (p.1 : G) *
            (lampPerm (M := M) d p.2 *
              basePerm (M := M) (α := α) d (q.1 : G)) *
              lampPerm (M := M) d q.2 := by
          rw [(edge_commutes_lamp M d q.1 p.2).eq]
      _ = (basePerm (M := M) (α := α) d (p.1 : G) *
            lampPerm (M := M) d p.2) *
          (basePerm (M := M) (α := α) d (q.1 : G) *
            lampPerm (M := M) d q.2) := by group

/-- The two factor actions defining the free-lamp action. -/
def factorPerm
    (d : HNNExtension.NormalWord.TransversalPair G M M) : ∀ b,
    LampFactor G M (FreeGroup α) b →*
      Equiv.Perm (Space (M := M) (α := α) d)
  | true => basePermHom (M := M) (α := α) d
  | false => lampFactorPerm (M := M) d

theorem factorPerm_comp
    (d : HNNExtension.NormalWord.TransversalPair G M M) : ∀ b,
    (factorPerm (M := M) (α := α) d b).comp
        (lampMap G M (FreeGroup α) b) =
      (basePermHom (M := M) (α := α) d).comp M.subtype := by
  intro b
  cases b with
  | false =>
      apply MonoidHom.ext
      intro m
      change basePerm (M := M) (α := α) d (m : G) *
          lampPerm (M := M) d 1 = basePerm (M := M) (α := α) d (m : G)
      rw [show lampPerm (M := M) d 1 = 1 by
        exact map_one (lampPermHom (M := M) d)]
      exact mul_one _
  | true => rfl

/-- The free-label permutation action of a free lamp. -/
def action
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeLamp G M (FreeGroup α) →*
      Equiv.Perm (Space (M := M) (α := α) d) :=
  PushoutI.lift (factorPerm (M := M) (α := α) d)
    ((basePermHom (M := M) (α := α) d).comp M.subtype)
    (factorPerm_comp (M := M) (α := α) d)

@[simp] theorem action_inAmbient
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    action (M := M) (α := α) d (inAmbient G M (FreeGroup α) g) =
      basePerm (M := M) (α := α) d g := by
  exact PushoutI.lift_of _ _ _ _

@[simp] theorem action_inLamp
    (d : HNNExtension.NormalWord.TransversalPair G M M) (k : FreeGroup α) :
    action (M := M) (α := α) d (inLamp G M (FreeGroup α) k) =
      lampPerm (M := M) d k := by
  change PushoutI.lift _ _ _
      (PushoutI.of (φ := lampMap G M (FreeGroup α)) false ((1 : M), k)) = _
  rw [PushoutI.lift_of]
  change basePerm (M := M) (α := α) d 1 * lampPerm (M := M) d k = _
  rw [show basePerm (M := M) (α := α) d 1 = 1 by
    exact map_one (basePermHom (M := M) (α := α) d), one_mul]

end

end FreeLampFiniteBaseProfinite
end Higman
end GroupApproximation
