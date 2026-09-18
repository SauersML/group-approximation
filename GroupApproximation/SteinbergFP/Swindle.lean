import GroupApproximation.SteinbergFP.Intertwine
import GroupApproximation.SteinbergFP.Room
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The Leavitt swindle: `E_V(F)` embeds in `St_{3|V|+1}(S)`

Let `S` be a ring with a binary Leavitt family `L`, and let `φ : F →+* S` be an injective ring
homomorphism whose image commutes with `t₀, t₁`.  Put `U = Fin 3 × V` and adjoin one index,
`T = Option U`.
The homomorphism

    Φ : St_V(F) → St_T(S),   x_ij(a) ↦ x_{(0,i),(0,j)}(φ a)

has kernel exactly `K₂(V, F)` whenever `St_V(F)` is perfect (`stab_rowMap_zero_eq_one_iff`).
So `E_V(F) = St_V(F) / K₂(V, F)` embeds in `St_T(S)` (`exists_injective_elementary`).

The proof is the research node `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`.

* The block swap `ω` intertwines the base copy with the Leavitt doubled copy on elementary
  matrices (`stMatrix_conj_swap`).  So `c(g) = Φ'(ω g ω⁻¹)⁻¹ · Φ'(double g)` has trivial matrix,
  and after adjoining the room index it is central (`indexMap_some_mem_center`).
* A central-valued `c` is a homomorphism, and it vanishes because `St_V(F)` is perfect.
* On `K₂(V, F)` the base copy is itself central, so conjugation by `ω` fixes it.  Since the image
  of `φ` commutes with `t₀, t₁`, the doubled copy of `x_ij(φ a)` is the product of the base copy and its
  row-`1` copy.  Comparing gives that the row-`1` copy of `k ∈ K₂(V, F)` is trivial, and so is
  the base copy, which differs from it by a relabelling.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open scoped commutatorElement
open SteinbergGroup

section Perfect

/-- A central-valued homomorphism out of a perfect group is trivial. -/
theorem hom_eq_one_of_central {G T : Type*} [Group G] [Group T] [Group.IsPerfect G]
    (c : G →* T) (hc : ∀ g, c g ∈ Subgroup.center T) (g : G) : c g = 1 := by
  have hle : commutator G ≤ c.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨p, q, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp (hc p) (c q)).symm
  exact MonoidHom.mem_ker.mp (hle Group.IsPerfect.mem_commutator)

/-- The cocycle identity for a central left factor. -/
theorem mul_center_swindle {G : Type*} [Group G] (a₁ a₂ b₁ b₂ : G)
    (hc : a₁⁻¹ * b₁ ∈ Subgroup.center G) :
    (a₁ * a₂)⁻¹ * (b₁ * b₂) = (a₁⁻¹ * b₁) * (a₂⁻¹ * b₂) := by
  calc (a₁ * a₂)⁻¹ * (b₁ * b₂) = a₂⁻¹ * (a₁⁻¹ * b₁) * b₂ := by group
    _ = (a₁⁻¹ * b₁) * a₂⁻¹ * b₂ := by rw [Subgroup.mem_center_iff.mp hc a₂⁻¹]
    _ = (a₁⁻¹ * b₁) * (a₂⁻¹ * b₂) := by group

end Perfect

variable {V F S : Type*} [Fintype V] [DecidableEq V] [Ring F] [Ring S]

/-- The elementary matrix of `ringMap φ g` is the entrywise image of that of `g`. -/
theorem stMatrix_ringMap (φ : F →+* S) (g : SteinbergGroup V F) :
    stMatrix V S (ringMap φ g) = (stMatrix V F g).map φ := by
  have h : (stMatrix V S).comp (ringMap (I := V) φ) =
      (RingHom.mapMatrix (m := V) φ).toMonoidHom.comp (stMatrix V F) := by
    apply hom_ext_of_x
    intro a b hab r
    change stMatrix V S (ringMap φ (x a b hab r)) = (stMatrix V F (x a b hab r)).map φ
    rw [ringMap_x, stMatrix_x, stMatrix_x]
    ext p q
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp
  exact DFunLike.congr_fun h g

variable (L : LeavittFamily S) (φ : F →+* S)

/-- Row `r`: `i ↦ (r, i)`. -/
def rowEmb (r : Fin 3) : V ↪ Fin 3 × V := ⟨fun i ↦ (r, i), fun _ _ h ↦ (Prod.mk.inj h).2⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem rowEmb_apply (r : Fin 3) (i : V) : rowEmb r i = (r, i) := rfl

omit [Fintype V] [DecidableEq V] in
theorem rowEmb_zero : rowEmb (V := V) 0 = baseEmb := rfl

/-- Adjoining the room index. -/
abbrev stab : SteinbergGroup (Fin 3 × V) S →* SteinbergGroup (Option (Fin 3 × V)) S :=
  indexMap Function.Embedding.some

/-- The row-`r` copy `x_ij(a) ↦ x_{(r,i),(r,j)}(φ a)`. -/
def rowMap (r : Fin 3) : SteinbergGroup V F →* SteinbergGroup (Fin 3 × V) S :=
  (indexMap (rowEmb r)).comp (ringMap φ)

/-- The doubled copy `g ↦ δ(double L (φ_* g))`. -/
def dblMap : SteinbergGroup V F →* SteinbergGroup (Fin 3 × V) S :=
  (indexMap dblEmb).comp ((double L).comp (ringMap φ))

theorem rowMap_commute (g h : SteinbergGroup V F) :
    Commute (rowMap φ 0 g) (rowMap φ 1 h) :=
  commute_indexMap_of_disjoint (rowEmb 0) (rowEmb 1) (fun a c e ↦ by
    have h0 : ((0 : Fin 3), a) = ((1 : Fin 3), c) := e
    have h1 : (0 : Fin 3) = 1 := congrArg Prod.fst h0
    exact absurd h1 (by decide)) (ringMap φ g) (ringMap φ h)

theorem rowMap_stMatrix_eq_one {k : SteinbergGroup V F} (hk : stMatrix V F k = 1) (r : Fin 3) :
    stMatrix (Fin 3 × V) S (rowMap φ r k) = 1 := by
  rw [rowMap, MonoidHom.comp_apply, stMatrix_indexMap_eq_one_iff, stMatrix_ringMap, hk,
    Matrix.map_one φ (map_zero φ) (map_one φ)]

/-- `ψ(c)` is the scalar matrix `c` when `c` commutes with `t₀` and `t₁`. -/
theorem psi_of_commute {c : S} (hc : ∀ s : Fin 2, L.tv s * c = c * L.tv s) (s t : Fin 2) :
    L.psi c s t = if s = t then c else 0 := by
  simp only [LeavittFamily.psi, Matrix.of_apply]
  rw [hc s, mul_assoc, L.tv_mul_sv]
  split_ifs <;> simp

/-- When `φ` commutes with `t₀, t₁`, the doubled copy is the product of rows `0` and `1`. -/
theorem dblMap_eq_mul (hφ : ∀ a (s : Fin 2), L.tv s * φ a = φ a * L.tv s)
    (g : SteinbergGroup V F) :
    dblMap L φ g = rowMap φ 0 g * rowMap φ 1 g := by
  have h : dblMap L φ = ((rowMap φ 0).noncommCoprod (rowMap φ 1) (rowMap_commute φ)).comp
      ((MonoidHom.id (SteinbergGroup V F)).prod (MonoidHom.id (SteinbergGroup V F))) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change dblMap L φ (x i j hij a) = rowMap φ 0 (x i j hij a) * rowMap φ 1 (x i j hij a)
    have h00 : L.psi (φ a) 0 0 = φ a := by rw [psi_of_commute L (hφ a)]; simp
    have h01 : L.psi (φ a) 0 1 = 0 := by rw [psi_of_commute L (hφ a)]; simp
    have h10 : L.psi (φ a) 1 0 = 0 := by rw [psi_of_commute L (hφ a)]; simp
    have h11 : L.psi (φ a) 1 1 = φ a := by rw [psi_of_commute L (hφ a)]; simp
    simp only [dblMap, rowMap, MonoidHom.comp_apply, ringMap_x, double_x, blk, dx, h00, h01, h10,
      h11, x_zero, mul_one, map_mul, indexMap_x]
    congr 1
  rw [h]
  simp [MonoidHom.noncommCoprod_apply]

theorem conj_rowMap_stMatrix (g : SteinbergGroup V F) :
    stMatrix (Fin 3 × V) S
      ((blockSwap L * rowMap φ 0 g * (blockSwap L)⁻¹)⁻¹ * dblMap L φ g) = 1 := by
  have h : stMatrix (Fin 3 × V) S (blockSwap L * rowMap φ 0 g * (blockSwap L)⁻¹) =
      stMatrix (Fin 3 × V) S (dblMap L φ g) :=
    stMatrix_conj_swap L (ringMap φ g)
  rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]

/-- The swindle cocycle. -/
def cfun (g : SteinbergGroup V F) : SteinbergGroup (Option (Fin 3 × V)) S :=
  (stab (blockSwap L * rowMap φ 0 g * (blockSwap L)⁻¹))⁻¹ * stab (dblMap L φ g)

theorem cfun_mem_center (g : SteinbergGroup V F) :
    cfun L φ g ∈ Subgroup.center (SteinbergGroup (Option (Fin 3 × V)) S) := by
  have h := indexMap_some_mem_center (conj_rowMap_stMatrix L φ g)
  unfold cfun
  simp only [map_mul, map_inv] at h ⊢
  exact h

theorem cfun_mul (g h : SteinbergGroup V F) : cfun L φ (g * h) = cfun L φ g * cfun L φ h := by
  have hA : blockSwap L * rowMap φ 0 (g * h) * (blockSwap L)⁻¹ =
      (blockSwap L * rowMap φ 0 g * (blockSwap L)⁻¹) *
        (blockSwap L * rowMap φ 0 h * (blockSwap L)⁻¹) := by
    rw [map_mul]
    group
  have ha : stab (blockSwap L * rowMap φ 0 (g * h) * (blockSwap L)⁻¹) =
      stab (blockSwap L * rowMap φ 0 g * (blockSwap L)⁻¹) *
        stab (blockSwap L * rowMap φ 0 h * (blockSwap L)⁻¹) := by
    rw [hA]
    exact map_mul _ _ _
  have hb : stab (dblMap L φ (g * h)) = stab (dblMap L φ g) * stab (dblMap L φ h) := by
    rw [map_mul (dblMap L φ)]
    exact map_mul _ _ _
  unfold cfun
  rw [ha, hb]
  exact mul_center_swindle _ _ _ _ (cfun_mem_center L φ g)

/-- The swindle cocycle as a homomorphism. -/
def cHom : SteinbergGroup V F →* SteinbergGroup (Option (Fin 3 × V)) S where
  toFun := cfun L φ
  map_one' := by simp [cfun]
  map_mul' := cfun_mul L φ

/-- **Swindle, step 1.**  After adjoining the room index, `ω` conjugates the base copy to the
doubled copy. -/
theorem stab_conj_eq [Group.IsPerfect (SteinbergGroup V F)] (g : SteinbergGroup V F) :
    stab (blockSwap L * rowMap φ 0 g * (blockSwap L)⁻¹) = stab (dblMap L φ g) := by
  have h : cfun L φ g = 1 := hom_eq_one_of_central (cHom L φ) (cfun_mem_center L φ) g
  unfold cfun at h
  exact inv_mul_eq_one.mp h

/-- Swap rows `0` and `1`. -/
def rowSwap : Option (Fin 3 × V) ≃ Option (Fin 3 × V) :=
  Equiv.optionCongr (Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl V))

theorem stab_rowMap_one (g : SteinbergGroup V F) :
    stab (rowMap φ 1 g) = reindexEquiv rowSwap (stab (S := S) (rowMap φ 0 g)) := by
  have h : (stab (V := V) (S := S)).comp (rowMap φ 1) =
      (reindexEquiv rowSwap).toMonoidHom.comp ((stab (V := V) (S := S)).comp (rowMap φ 0)) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change indexMap _ (indexMap (rowEmb 1) (ringMap φ (x i j hij a))) =
      indexMap rowSwap.toEmbedding
        (indexMap Function.Embedding.some (indexMap (rowEmb 0) (ringMap φ (x i j hij a))))
    simp only [ringMap_x, indexMap_x]
    apply x_congr <;> simp [rowSwap]
  exact DFunLike.congr_fun h g

/-- **Swindle, step 2.**  The base copy kills `K₂(V, F)` after adjoining the room index. -/
theorem stab_rowMap_zero_eq_one [Group.IsPerfect (SteinbergGroup V F)]
    (hφ : ∀ a (s : Fin 2), L.tv s * φ a = φ a * L.tv s) {k : SteinbergGroup V F}
    (hk : stMatrix V F k = 1) :
    stab (rowMap φ 0 k) = 1 := by
  have hc0 : stab (rowMap φ 0 k) ∈ Subgroup.center (SteinbergGroup (Option (Fin 3 × V)) S) :=
    indexMap_some_mem_center (rowMap_stMatrix_eq_one φ hk 0)
  have h1 : stab (blockSwap L * rowMap φ 0 k * (blockSwap L)⁻¹) = stab (rowMap φ 0 k) := by
    have hc := Subgroup.mem_center_iff.mp hc0 (stab (blockSwap L))
    rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
  have h2 := stab_conj_eq L φ k
  rw [h1, dblMap_eq_mul L φ hφ, map_mul] at h2
  have h3 : stab (rowMap φ 1 k) = 1 := left_eq_mul.mp h2
  rw [stab_rowMap_one] at h3
  exact (MulEquiv.map_eq_one_iff _).mp h3

/-- **The kernel of the base copy is `K₂(V, F)`.** -/
theorem stab_rowMap_zero_eq_one_iff [Group.IsPerfect (SteinbergGroup V F)]
    (hφ : ∀ a (s : Fin 2), L.tv s * φ a = φ a * L.tv s) (hinj : Function.Injective φ)
    (g : SteinbergGroup V F) :
    stab (rowMap φ 0 g) = 1 ↔ projection g = 1 := by
  rw [projection_eq_one_iff]
  constructor
  · intro h
    have h' := congrArg (stMatrix (Option (Fin 3 × V)) S) h
    rw [map_one, stMatrix_indexMap_eq_one_iff, rowMap, MonoidHom.comp_apply,
      stMatrix_indexMap_eq_one_iff, stMatrix_ringMap] at h'
    exact Matrix.map_injective hinj (h'.trans (Matrix.map_one φ (map_zero φ) (map_one φ)).symm)
  · exact stab_rowMap_zero_eq_one L φ hφ

/-- **`E_V(F)` embeds in `St_{Option (Fin 3 × V)}(S)`.** -/
theorem exists_injective_elementary [Group.IsPerfect (SteinbergGroup V F)]
    (hφ : ∀ a (s : Fin 2), L.tv s * φ a = φ a * L.tv s) (hinj : Function.Injective φ) :
    ∃ f : elementaryGroup V F →* SteinbergGroup (Option (Fin 3 × V)) S,
      Function.Injective f := by
  let Φ : SteinbergGroup V F →* SteinbergGroup (Option (Fin 3 × V)) S := stab.comp (rowMap φ 0)
  have hker : (projection (I := V) (R := F)).ker = Φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (stab_rowMap_zero_eq_one_iff L φ hφ hinj g).symm
  let e₁ : elementaryGroup V F ≃* SteinbergGroup V F ⧸ (projection (I := V) (R := F)).ker :=
    (QuotientGroup.quotientKerEquivOfSurjective _ projection_surjective).symm
  let e₂ := QuotientGroup.quotientMulEquivOfEq hker
  refine ⟨(QuotientGroup.kerLift Φ).comp (e₂.toMonoidHom.comp e₁.toMonoidHom), ?_⟩
  exact (QuotientGroup.kerLift_injective Φ).comp (e₂.injective.comp e₁.injective)

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.stab_rowMap_zero_eq_one_iff
#audit_axioms GroupApproximation.SteinbergFP.exists_injective_elementary
