import GroupApproximation.Higman.PairedReturnCutter

/-!
# The paired-return edge is an honest graph

The four-generator edge in `PairedReturnCutter` is the image of two copies of
`K = ⟨b,c⟩`.  Its first coordinate sends the first copy identically into
`K` and the second copy into `a K a⁻¹`.  This file proves that first-coordinate
map is injective by an explicit two-state action.  Consequently the edge is
literally the graph of the homomorphism which kills the first copy and retains
the second copy.

This is the algebraic input needed before one can address profinite
separability of the edge inside `F₃ × F₃`.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnEdgeGraph

open scoped Monoid.Coprod
open Conj

abbrev Sync : Type := ↥K
abbrev Double : Type := Monoid.Coprod Sync Sync
abbrev StateSpace : Type := Double × Bool

/-- Write a `K`-letter in the copy selected by the Boolean state. -/
def sideHom (s : Bool) : Sync →* Double :=
  if s then Monoid.Coprod.inr else Monoid.Coprod.inl

@[simp] theorem sideHom_false :
    sideHom false = (Monoid.Coprod.inl : Sync →* Double) := rfl

@[simp] theorem sideHom_true :
    sideHom true = (Monoid.Coprod.inr : Sync →* Double) := rfl

/-- A `K`-letter writes in the copy selected by the current state. -/
def writePerm (h : Sync) : Equiv.Perm StateSpace where
  toFun p := (sideHom p.2 h * p.1, p.2)
  invFun p := ((sideHom p.2 h)⁻¹ * p.1, p.2)
  left_inv p := by rcases p with ⟨w, s⟩; apply Prod.ext <;> simp
  right_inv p := by rcases p with ⟨w, s⟩; apply Prod.ext <;> simp

@[simp] theorem writePerm_apply (h : Sync) (w : Double) (s : Bool) :
    writePerm h (w, s) = (sideHom s h * w, s) := rfl

/-- The letter `a` toggles which copy receives subsequent `K`-letters. -/
def togglePerm : Equiv.Perm StateSpace where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv p := by rcases p with ⟨w, s⟩; cases s <;> rfl
  right_inv p := by rcases p with ⟨w, s⟩; cases s <;> rfl

@[simp] theorem togglePerm_apply (w : Double) (s : Bool) :
    togglePerm (w, s) = (w, !s) := rfl

@[simp] theorem togglePerm_symm_apply (w : Double) (s : Bool) :
    togglePerm.symm (w, s) = (w, !s) := rfl

/-- The two-state action of `F₃`. -/
def act : F₃ →* Equiv.Perm StateSpace :=
  FreeGroup.lift fun i : Fin 3 ↦
    if i = 0 then togglePerm
    else if i = 1 then writePerm PairedReturnCutter.bSync
    else writePerm PairedReturnCutter.cSync

@[simp] theorem act_a : act a = togglePerm := by
  simp [act, a]

@[simp] theorem act_b : act b = writePerm PairedReturnCutter.bSync := by
  simp [act, b]

@[simp] theorem act_c : act c = writePerm PairedReturnCutter.cSync := by
  simp [act, c]

/-- Every element of `K` writes in the copy selected by the current state. -/
theorem act_of_mem_K {x : F₃} (hx : x ∈ K) (w : Double) (s : Bool) :
    act x (w, s) =
      (sideHom s (⟨x, hx⟩ : Sync) * w, s) := by
  induction hx using Subgroup.closure_induction generalizing w s with
  | mem y hy =>
      rcases hy with rfl | hy
      · rw [act_b]
        rfl
      · rw [Set.mem_singleton_iff] at hy
        subst y
        rw [act_c]
        rfl
  | one =>
      rw [map_one]
      apply Prod.ext
      · change w = sideHom s (1 : Sync) * w
        rw [map_one, one_mul]
      · rfl
  | mul y z hy hz ihy ihz =>
      rw [map_mul]
      change act y (act z (w, s)) = _
      rw [ihz, ihy]
      apply Prod.ext
      · change sideHom s ⟨y, hy⟩ * (sideHom s ⟨z, hz⟩ * w) =
          sideHom s ⟨y * z, K.mul_mem hy hz⟩ * w
        rw [← mul_assoc]
        have hm := (sideHom s).map_mul
          (⟨y, by simpa only [K] using hy⟩ : Sync)
          (⟨z, by simpa only [K] using hz⟩ : Sync)
        rw [← hm]
        congr 2
      · rfl
  | inv y hy ihy =>
      rw [map_inv]
      apply (act y).symm_apply_eq.mpr
      change (w, s) = act y (sideHom s ⟨y⁻¹, K.inv_mem hy⟩ * w, s)
      rw [ihy]
      apply Prod.ext
      · change w = sideHom s ⟨y, hy⟩ *
          (sideHom s ⟨y⁻¹, K.inv_mem hy⟩ * w)
        have hinv : sideHom s ⟨y⁻¹, K.inv_mem hy⟩ =
            (sideHom s ⟨y, hy⟩)⁻¹ := by
          exact map_inv (sideHom s) ⟨y, hy⟩
        rw [hinv]
        group
      · rfl

/-- The first coordinate of the paired-return edge parametrization. -/
def firstPath : Double →* F₃ :=
  Monoid.Coprod.lift K.subtype
    { toFun := fun h ↦ a * (h : F₃) * a⁻¹
      map_one' := by simp
      map_mul' := by intro h k; simp only [Subgroup.coe_mul]; group }

@[simp] theorem firstPath_inl (h : Sync) :
    firstPath (Monoid.Coprod.inl h) = (h : F₃) := by
  rw [firstPath, Monoid.Coprod.lift_apply_inl]
  rfl

@[simp] theorem firstPath_inr (h : Sync) :
    firstPath (Monoid.Coprod.inr h) = a * (h : F₃) * a⁻¹ := by
  rw [firstPath, Monoid.Coprod.lift_apply_inr]
  rfl

/-- The action reads back a word in the two copies from its first-coordinate
image. -/
theorem act_firstPath (z : Double) (w : Double) :
    act (firstPath z) (w, false) = (z * w, false) := by
  induction z using Monoid.Coprod.induction_on generalizing w with
  | inl h =>
      rw [firstPath_inl, act_of_mem_K h.property]
      rfl
  | inr h =>
      rw [firstPath_inr, map_mul, map_mul, map_inv, act_a]
      change togglePerm
          (act (h : F₃) (togglePerm.symm (w, false))) =
        (Monoid.Coprod.inr h * w, false)
      rw [togglePerm_symm_apply, act_of_mem_K h.property, togglePerm_apply]
      rfl
  | mul x y hx hy =>
      rw [map_mul, map_mul]
      change act (firstPath x) (act (firstPath y) (w, false)) = _
      rw [hy, hx]
      apply Prod.ext
      · group
      · rfl

/-- The first coordinate alone faithfully records the two-copy word. -/
theorem firstPath_injective : Function.Injective firstPath := by
  intro x y hxy
  have hact := congrArg act hxy
  have hp := DFunLike.congr_fun hact ((1 : Double), false)
  rw [act_firstPath, act_firstPath] at hp
  have := congrArg Prod.fst hp
  simpa using this

/-- The second coordinate forgets the first copy and embeds the second. -/
def secondPath : Double →* F₃ :=
  Monoid.Coprod.lift 1 K.subtype

@[simp] theorem secondPath_inl (h : Sync) :
    secondPath (Monoid.Coprod.inl h) = 1 := by
  rw [secondPath, Monoid.Coprod.lift_apply_inl]
  rfl

@[simp] theorem secondPath_inr (h : Sync) :
    secondPath (Monoid.Coprod.inr h) = (h : F₃) := by
  rw [secondPath, Monoid.Coprod.lift_apply_inr]
  rfl

/-- The original edge map is the graph of `secondPath` over the embedded
first path. -/
theorem mu_eq_graph (z : Double) :
    PairedReturnGraphIntersection.mu z =
      (firstPath z, secondPath z) := by
  induction z using Monoid.Coprod.induction_on with
  | inl h => simp [PairedReturnGraphIntersection.alpha]
  | inr h => simp [PairedReturnGraphIntersection.beta]
  | mul x y hx hy =>
      rw [map_mul, map_mul, map_mul, hx, hy]
      rfl

/-- In particular, the parametrization of the four-generator edge is
injective. -/
theorem mu_injective :
    Function.Injective PairedReturnGraphIntersection.mu := by
  intro x y hxy
  apply firstPath_injective
  simpa only [mu_eq_graph] using congrArg Prod.fst hxy

/-- The edge subgroup is canonically the two-copy free product. -/
noncomputable def doubleEquivEdge :
    Double ≃* PairedReturnCutter.Edge :=
  MulEquiv.ofBijective PairedReturnGraphIntersection.mu.rangeRestrict
    ⟨fun _ _ h ↦ mu_injective (Subtype.ext_iff.mp h),
      MonoidHom.rangeRestrict_surjective _⟩

end PairedReturnEdgeGraph
end Higman
end GroupApproximation
