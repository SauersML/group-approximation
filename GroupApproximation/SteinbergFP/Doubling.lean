import GroupApproximation.Steinberg.Basic
import GroupApproximation.Leavitt.Leavitt
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Matrix.Mul
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leavitt doubling homomorphism `St_V(S) → St_{V × Fin 2}(S)`

Let `S` be a ring with a binary Leavitt family `s₀, s₁, t₀, t₁` (`tᵢ sⱼ = δᵢⱼ`,
`s₀ t₀ + s₁ t₁ = 1`).  The map `ψ : S → M₂(S)`, `ψ(a)_{st} = t_s a s_t`, is multiplicative and
additive.  Block expansion of `ψ` gives, on Steinberg generators,

    x_{ij}(a) ↦ ∏_{s,t} x_{(i,s),(j,t)}(t_s a s_t),

and the three Steinberg relations are checked here directly, so this defines the doubling
homomorphism `double L : St_V(S) →* St_{V × Fin 2}(S)`.  This is step (b) of the research node
`leavitt-pairs-embed-sl-n-q-in-steinberg-groups`.

The block roots `blk hij M = ∏_{s,t} x_{(i,s),(j,t)}(M s t)` satisfy
`blk M * blk M' = blk (M + M')`, commute across non-adjacent pairs, and
`⁅blk_{ij} M, blk_{jk} M'⁆ = blk_{ik} (M * M')`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open scoped commutatorElement
open SteinbergGroup

/-! ## Two commutator identities -/

section Comm

variable {G : Type*} [Group G]

theorem comm_mul_left_of {a b c : G} (h : Commute a ⁅b, c⁆) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  have : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [this, h.eq, mul_inv_cancel_right]

theorem comm_mul_right_of {a b c : G} (h : Commute b ⁅a, c⁆) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this, h.eq, mul_inv_cancel_right]

theorem commute_prod4_left {a₁ a₂ a₃ a₄ c : G} (h₁ : Commute a₁ c) (h₂ : Commute a₂ c)
    (h₃ : Commute a₃ c) (h₄ : Commute a₄ c) : Commute (a₁ * a₂ * a₃ * a₄) c :=
  ((h₁.mul_left h₂).mul_left h₃).mul_left h₄

theorem commute_prod4_right {c a₁ a₂ a₃ a₄ : G} (h₁ : Commute c a₁) (h₂ : Commute c a₂)
    (h₃ : Commute c a₃) (h₄ : Commute c a₄) : Commute c (a₁ * a₂ * a₃ * a₄) :=
  ((h₁.mul_right h₂).mul_right h₃).mul_right h₄

/-- Four pairwise commuting pairs can be interleaved. -/
theorem prod4_mul_prod4 {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : G}
    (h₂₁ : Commute a₂ b₁) (h₃₁ : Commute a₃ b₁) (h₄₁ : Commute a₄ b₁)
    (h₃₂ : Commute a₃ b₂) (h₄₂ : Commute a₄ b₂) (h₄₃ : Commute a₄ b₃) :
    a₁ * a₂ * a₃ * a₄ * (b₁ * b₂ * b₃ * b₄) =
      a₁ * b₁ * (a₂ * b₂) * (a₃ * b₃) * (a₄ * b₄) := by
  have e1 : a₂ * a₃ * a₄ * b₁ = b₁ * (a₂ * a₃ * a₄) :=
    ((h₂₁.mul_left h₃₁).mul_left h₄₁).eq
  have e2 : a₃ * a₄ * b₂ = b₂ * (a₃ * a₄) := (h₃₂.mul_left h₄₂).eq
  have e3 : a₄ * b₃ = b₃ * a₄ := h₄₃.eq
  calc a₁ * a₂ * a₃ * a₄ * (b₁ * b₂ * b₃ * b₄)
      = a₁ * (a₂ * a₃ * a₄ * b₁) * (b₂ * b₃ * b₄) := by group
    _ = a₁ * b₁ * (a₂ * (a₃ * a₄ * b₂)) * (b₃ * b₄) := by rw [e1]; group
    _ = a₁ * b₁ * (a₂ * b₂) * (a₃ * (a₄ * b₃)) * b₄ := by rw [e2]; group
    _ = a₁ * b₁ * (a₂ * b₂) * (a₃ * b₃) * (a₄ * b₄) := by rw [e3]; group

end Comm

/-! ## Block roots -/

variable {V S : Type*} [Fintype V] [DecidableEq V] [Ring S]

omit [Fintype V] [DecidableEq V] in
theorem pair_ne {i j : V} (hij : i ≠ j) (s t : Fin 2) : (i, s) ≠ (j, t) :=
  fun h ↦ hij (Prod.mk.inj h).1

/-- `x_{(i,s),(j,t)}(c)` in `St_{V × Fin 2}(S)`. -/
abbrev dx {i j : V} (hij : i ≠ j) (s t : Fin 2) (c : S) : SteinbergGroup (V × Fin 2) S :=
  x (i, s) (j, t) (pair_ne hij s t) c

/-- The block root `∏_{s,t} x_{(i,s),(j,t)}(M s t)`. -/
def blk {i j : V} (hij : i ≠ j) (M : Matrix (Fin 2) (Fin 2) S) :
    SteinbergGroup (V × Fin 2) S :=
  dx hij 0 0 (M 0 0) * dx hij 0 1 (M 0 1) * dx hij 1 0 (M 1 0) * dx hij 1 1 (M 1 1)

theorem dx_commute_same {i j : V} (hij : i ≠ j) (s t s' t' : Fin 2) (c c' : S) :
    Commute (dx hij s t c) (dx hij s' t' c') :=
  x_commute_of_ne _ _ _ _ _ _ (pair_ne hij.symm t s') (pair_ne hij.symm t' s) c c'

theorem blk_mul {i j : V} (hij : i ≠ j) (M M' : Matrix (Fin 2) (Fin 2) S) :
    blk hij M * blk hij M' = blk hij (M + M') := by
  unfold blk
  rw [prod4_mul_prod4 (dx_commute_same hij _ _ _ _ _ _) (dx_commute_same hij _ _ _ _ _ _)
    (dx_commute_same hij _ _ _ _ _ _) (dx_commute_same hij _ _ _ _ _ _)
    (dx_commute_same hij _ _ _ _ _ _) (dx_commute_same hij _ _ _ _ _ _)]
  simp only [dx, x_mul, Matrix.add_apply]

theorem blk_zero {i j : V} (hij : i ≠ j) : blk hij (0 : Matrix (Fin 2) (Fin 2) S) = 1 := by
  simp [blk]

theorem dx_commute_of {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (s t u v : Fin 2) (c c' : S) : Commute (dx hij s t c) (dx hkl u v c') :=
  x_commute_of_ne _ _ _ _ _ _ (pair_ne hjk t u) (pair_ne hli v s) c c'

theorem dx_commute_blk {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (s t : Fin 2) (c : S) (M : Matrix (Fin 2) (Fin 2) S) :
    Commute (dx hij s t c) (blk hkl M) :=
  commute_prod4_right (dx_commute_of hij hkl hjk hli _ _ _ _ _ _)
    (dx_commute_of hij hkl hjk hli _ _ _ _ _ _) (dx_commute_of hij hkl hjk hli _ _ _ _ _ _)
    (dx_commute_of hij hkl hjk hli _ _ _ _ _ _)

theorem blk_commute {i j k l : V} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (M M' : Matrix (Fin 2) (Fin 2) S) : Commute (blk hij M) (blk hkl M') :=
  commute_prod4_left (dx_commute_blk hij hkl hjk hli _ _ _ _)
    (dx_commute_blk hij hkl hjk hli _ _ _ _) (dx_commute_blk hij hkl hjk hli _ _ _ _)
    (dx_commute_blk hij hkl hjk hli _ _ _ _)

/-- The single-row matrix with row `s` equal to `M s t • M' t ·`. -/
def rowProd (M M' : Matrix (Fin 2) (Fin 2) S) (s t : Fin 2) : Matrix (Fin 2) (Fin 2) S :=
  Matrix.of fun s' u ↦ if s' = s then M s t * M' t u else 0

section Adjacent

variable {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)

/-- `⁅x_{(i,s),(j,t)}(c), x_{(j,t'),(k,u)}(c')⁆` is `x_{(i,s),(k,u)}(c c')` if `t = t'`, and `1`
otherwise. -/
theorem dx_comm_dx (s t t' u : Fin 2) (c c' : S) :
    ⁅dx hij s t c, dx hjk t' u c'⁆ = if t = t' then dx hik s u (c * c') else 1 := by
  split_ifs with h
  · subst h
    exact x_commutator _ _ _ _ _ (pair_ne hik s u) c c'
  · exact (x_commute_of_ne _ _ _ _ _ _ (fun e ↦ h (Prod.mk.inj e).2)
      (pair_ne hik.symm u s) c c').commutator_eq


theorem dx_commute_jk_ik (s u t v : Fin 2) (c c' : S) :
    Commute (dx hjk t v c) (dx hik s u c') :=
  x_commute_of_ne _ _ _ _ _ _ (pair_ne hik.symm v s) (pair_ne hjk.symm u t) c c'

include hik in
/-- A root `x_{(j,t),(k,v)}` commutes with every `⁅x_{(i,s),(j,t₁)}(c), x_{(j,t'),(k,u)}(c')⁆`. -/
theorem dx_commute_comm (s t t' u t₁ v : Fin 2) (c c' c₁ : S) :
    Commute (dx hjk t₁ v c₁) ⁅dx hij s t c, dx hjk t' u c'⁆ := by
  rw [dx_comm_dx hij hjk hik]
  split_ifs
  · exact dx_commute_jk_ik hjk hik _ _ _ _ _ _
  · exact Commute.one_right _

theorem comm_prod4_right {G : Type*} [Group G] {a y₁ y₂ y₃ y₄ : G}
    (h₄ : Commute (y₁ * y₂ * y₃) ⁅a, y₄⁆) (h₃ : Commute (y₁ * y₂) ⁅a, y₃⁆)
    (h₂ : Commute y₁ ⁅a, y₂⁆) :
    ⁅a, y₁ * y₂ * y₃ * y₄⁆ = ⁅a, y₁⁆ * ⁅a, y₂⁆ * ⁅a, y₃⁆ * ⁅a, y₄⁆ := by
  rw [comm_mul_right_of h₄, comm_mul_right_of h₃, comm_mul_right_of h₂]

theorem comm_prod4_left {G : Type*} [Group G] {c x₁ x₂ x₃ x₄ : G}
    (h₄ : Commute (x₁ * x₂ * x₃) ⁅x₄, c⁆) (h₃ : Commute (x₁ * x₂) ⁅x₃, c⁆)
    (h₂ : Commute x₁ ⁅x₂, c⁆) :
    ⁅x₁ * x₂ * x₃ * x₄, c⁆ = ⁅x₄, c⁆ * ⁅x₃, c⁆ * ⁅x₂, c⁆ * ⁅x₁, c⁆ := by
  rw [comm_mul_left_of h₄, comm_mul_left_of h₃, comm_mul_left_of h₂]
  simp only [mul_assoc]

/-- Step A: the commutator of one root with a whole block root. -/
theorem dx_comm_blk (M M' : Matrix (Fin 2) (Fin 2) S) (s t : Fin 2) :
    ⁅dx hij s t (M s t), blk hjk M'⁆ = blk hik (rowProd M M' s t) := by
  unfold blk
  rw [comm_prod4_right]
  · simp only [dx_comm_dx hij hjk hik]
    fin_cases s <;> fin_cases t <;> simp [rowProd, dx]
  · exact ((dx_commute_comm hij hjk hik _ _ _ _ _ _ _ _ _).mul_left
      (dx_commute_comm hij hjk hik _ _ _ _ _ _ _ _ _)).mul_left
      (dx_commute_comm hij hjk hik _ _ _ _ _ _ _ _ _)
  · exact (dx_commute_comm hij hjk hik _ _ _ _ _ _ _ _ _).mul_left
      (dx_commute_comm hij hjk hik _ _ _ _ _ _ _ _ _)
  · exact dx_commute_comm hij hjk hik _ _ _ _ _ _ _ _ _

/-- Step B: the adjacent relation for block roots. -/
theorem blk_comm_blk (M M' : Matrix (Fin 2) (Fin 2) S) :
    ⁅blk hij M, blk hjk M'⁆ = blk hik (M * M') := by
  have hX : ∀ (s t : Fin 2) (c : S) (R : Matrix (Fin 2) (Fin 2) S),
      Commute (dx hij s t c) (blk hik R) := fun s t c R ↦
    dx_commute_blk hij hik hij.symm hik.symm s t c R
  conv_lhs => rw [blk]
  rw [comm_prod4_left, dx_comm_blk hij hjk hik, dx_comm_blk hij hjk hik,
    dx_comm_blk hij hjk hik, dx_comm_blk hij hjk hik, blk_mul, blk_mul, blk_mul]
  · congr 1
    ext s u
    fin_cases s <;> fin_cases u <;>
      simp [rowProd, Matrix.mul_apply, Fin.sum_univ_two] <;> abel
  · rw [dx_comm_blk hij hjk hik]
    exact ((hX _ _ _ _).mul_left (hX _ _ _ _)).mul_left (hX _ _ _ _)
  · rw [dx_comm_blk hij hjk hik]
    exact (hX _ _ _ _).mul_left (hX _ _ _ _)
  · rw [dx_comm_blk hij hjk hik]
    exact hX _ _ _ _

end Adjacent

/-! ## The doubling homomorphism -/

section LeavittHelpers

variable (L : LeavittFamily S)

/-- `s = (s₀, s₁)`. -/
def _root_.GroupApproximation.LeavittFamily.sv : Fin 2 → S := ![L.s0, L.s1]

/-- `t = (t₀, t₁)`. -/
def _root_.GroupApproximation.LeavittFamily.tv : Fin 2 → S := ![L.t0, L.t1]

theorem _root_.GroupApproximation.LeavittFamily.tv_mul_sv (a b : Fin 2) :
    L.tv a * L.sv b = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [LeavittFamily.tv, LeavittFamily.sv, L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]

/-- `ψ(a)_{st} = t_s a s_t`. -/
def _root_.GroupApproximation.LeavittFamily.psi (a : S) : Matrix (Fin 2) (Fin 2) S :=
  Matrix.of fun s t ↦ L.tv s * a * L.sv t

theorem _root_.GroupApproximation.LeavittFamily.psi_add (a b : S) :
    L.psi (a + b) = L.psi a + L.psi b := by
  ext s t
  simp [LeavittFamily.psi, mul_add, add_mul]

theorem _root_.GroupApproximation.LeavittFamily.psi_mul (a b : S) :
    L.psi a * L.psi b = L.psi (a * b) := by
  ext s u
  simp only [LeavittFamily.psi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  have hsum : L.sv 0 * L.tv 0 + L.sv 1 * L.tv 1 = 1 := by
    simpa [LeavittFamily.sv, LeavittFamily.tv] using L.sum_range
  calc L.tv s * a * L.sv 0 * (L.tv 0 * b * L.sv u) + L.tv s * a * L.sv 1 * (L.tv 1 * b * L.sv u)
      = L.tv s * a * (L.sv 0 * L.tv 0 + L.sv 1 * L.tv 1) * b * L.sv u := by noncomm_ring
    _ = L.tv s * (a * b) * L.sv u := by rw [hsum]; noncomm_ring

end LeavittHelpers

/-- The image of a Steinberg generator under doubling. -/
def doubleGen (L : LeavittFamily S) (g : SteinbergGenerator V S) :
    SteinbergGroup (V × Fin 2) S :=
  blk g.row_ne_column (L.psi g.coefficient)

private theorem doubleGen_kills_relations (L : LeavittFamily S)
    (w : FreeGroup (SteinbergGenerator V S)) (hw : w ∈ relations (I := V) (R := S)) :
    FreeGroup.lift (doubleGen L) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change blk hij (L.psi a) * blk hij (L.psi b) * (blk hij (L.psi (a + b)))⁻¹ = 1
      rw [blk_mul, ← L.psi_add, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅blk hij (L.psi a), blk hkl (L.psi b)⁆ = 1
      exact (blk_commute hij hkl hjk hli _ _).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅blk hij (L.psi a), blk hjk (L.psi b)⁆ * (blk hik (L.psi (a * b)))⁻¹ = 1
      rw [blk_comm_blk hij hjk hik, L.psi_mul, mul_inv_cancel]

/-- The Leavitt doubling homomorphism `St_V(S) →* St_{V × Fin 2}(S)`. -/
def double (L : LeavittFamily S) : SteinbergGroup V S →* SteinbergGroup (V × Fin 2) S :=
  PresentedGroup.toGroup (f := doubleGen L) (doubleGen_kills_relations L)

@[simp] theorem double_x (L : LeavittFamily S) (i j : V) (hij : i ≠ j) (a : S) :
    double L (x i j hij a) = blk hij (L.psi a) :=
  PresentedGroup.toGroup.of _

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.blk_comm_blk
#audit_axioms GroupApproximation.SteinbergFP.double
#audit_axioms GroupApproximation.SteinbergFP.double_x
