import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterModelSequence
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Abel

/-!
# The lamplighter action on the finite models

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602 (md5 0648e5f8…), tex 401–406, in the
proof of `cor:lef` and `cor:host`:

> Let `x ↦ δx + f` act on `Y_n = F_2^{Q'_n}` by `y ↦ σ_n(δ)y + ∑_{h ∈ supp f} 1_{σ_n(h)}`, where
> `(qy)(q') = y(q⁻¹q')`, and attach to `y` the point `y ∘ σ_n` of `Ω`.  For fixed elements of `Λ` and
> large `n`, these permutations multiply as in `Λ` and, uniformly in `y`, move the attached points
> near `e` as `Λ` moves the points of `Ω`.

For a sequence `M` of finite models of `Δ` (`BallModelSequence`):

* `ModelSpace M n = Y_n`, `qSmul M n q y = qy`, `lampImage M n f = ∑_h f(h) 1_{σ_n(h)}`, which is
  `∑_{h ∈ supp f} 1_{σ_n(h)}` over `F_2` (`lampImage_eq_sum_support`);
* `modelAct M n ξ`: the permutation `y ↦ σ_n(δ)y + ∑_{h ∈ supp f} 1_{σ_n(h)}` of `Y_n` for
  `ξ = (f, δ)`; `modelAct_one`, `modelAct_inr` (`y ↦ σ_n(δ)y`), `modelAct_lampAdd` (`y ↦ y + 1_e`);
* `attach M n y = y ∘ σ_n`;
* `eventually_modelAct_mul`: for fixed `ξ, η` and large `n`, `modelAct (ξη) = modelAct ξ ∘ modelAct η`;
* `eventually_attach_modelAct`: for fixed `ξ`, a finite set `J` of coordinates and large `n`,
  `attach (modelAct ξ y)` and `ξ • attach y` agree on `J` for every `y`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter

open Filter

variable {Δ : Type*} [Group Δ] {T : Set Δ} (M : BallModelSequence Δ T) (n : ℕ)

/-- `Y_n = F_2^{Q'_n}` (tex 401). -/
abbrev ModelSpace : Type _ :=
  M.Q n → ZMod 2

/-- `(q y)(q') = y(q⁻¹ q')` (tex 403). -/
def qSmul (q : M.Q n) (y : ModelSpace M n) : ModelSpace M n :=
  fun q' => y (q⁻¹ * q')

@[simp]
theorem qSmul_apply (q : M.Q n) (y : ModelSpace M n) (q' : M.Q n) :
    qSmul M n q y q' = y (q⁻¹ * q') :=
  rfl

theorem qSmul_qSmul (a b : M.Q n) (y : ModelSpace M n) :
    qSmul M n a (qSmul M n b y) = qSmul M n (a * b) y :=
  funext fun q' => by rw [qSmul_apply, qSmul_apply, qSmul_apply, mul_inv_rev, mul_assoc]

theorem qSmul_one (y : ModelSpace M n) : qSmul M n 1 y = y :=
  funext fun q' => by rw [qSmul_apply, inv_one, one_mul]

theorem qSmul_add (q : M.Q n) (y z : ModelSpace M n) :
    qSmul M n q (y + z) = qSmul M n q y + qSmul M n q z :=
  rfl

theorem qSmul_sum {ι : Type*} (q : M.Q n) (s : Finset ι) (f : ι → ModelSpace M n) :
    qSmul M n q (∑ i ∈ s, f i) = ∑ i ∈ s, qSmul M n q (f i) := by
  funext q'
  rw [qSmul_apply, Finset.sum_apply, Finset.sum_apply]
  rfl

theorem qSmul_single (q p : M.Q n) :
    qSmul M n q (Pi.single p (1 : ZMod 2)) = Pi.single (q * p) (1 : ZMod 2) := by
  funext q'
  rw [qSmul_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : q' = q * p
  · rw [if_pos (by rw [h, inv_mul_cancel_left]), if_pos h]
  · rw [if_neg (fun h' => h (by rw [← h', mul_inv_cancel_left])), if_neg h]

/-- The configuration `∑_h f(h) 1_{σ_n(h)}` on `Q'_n`. -/
noncomputable def lampImage (f : Δ →₀ ZMod 2) : ModelSpace M n :=
  f.sum fun h c => (Pi.single (M.σ n h) c : ModelSpace M n)

/-- **Over `F_2` it is `∑_{h ∈ supp f} 1_{σ_n(h)}`** (tex 402). -/
theorem lampImage_eq_sum_support (f : Δ →₀ ZMod 2) :
    lampImage M n f = ∑ h ∈ f.support, Pi.single (M.σ n h) (1 : ZMod 2) := by
  show ∑ h ∈ f.support, (Pi.single (M.σ n h) (f h) : ModelSpace M n) = _
  refine Finset.sum_congr rfl fun h hh => ?_
  rcases zmod_two_eq_zero_or_one (f h) with h0 | h1
  · exact absurd h0 (Finsupp.mem_support_iff.1 hh)
  · rw [h1]

theorem lampImage_zero : lampImage M n 0 = 0 :=
  Finsupp.sum_zero_index

theorem lampImage_add (f g : Δ →₀ ZMod 2) :
    lampImage M n (f + g) = lampImage M n f + lampImage M n g :=
  Finsupp.sum_add_index' (fun _ => Pi.single_zero _) fun _ _ _ => Pi.single_add _ _ _

theorem lampImage_single (a : Δ) (c : ZMod 2) :
    lampImage M n (Finsupp.single a c) = (Pi.single (M.σ n a) c : ModelSpace M n) :=
  Finsupp.sum_single_index (Pi.single_zero _)

/-- Translating the configuration by `δ` moves its image by `σ_n(δ)`, once `σ_n` is multiplicative
on `δ` and the support. -/
theorem lampImage_translate {δ : Δ} {F : Δ →₀ ZMod 2}
    (h : ∀ a ∈ F.support, M.σ n (δ * a) = M.σ n δ * M.σ n a) :
    lampImage M n (translate Δ δ F) = qSmul M n (M.σ n δ) (lampImage M n F) := by
  rw [lampImage_eq_sum_support, lampImage_eq_sum_support]
  show ∑ x ∈ F.support.map (leftMulEquiv Δ δ).toEmbedding,
      (Pi.single (M.σ n x) (1 : ZMod 2) : ModelSpace M n) = _
  rw [Finset.sum_map, qSmul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [qSmul_single, ← h a ha]
  rfl

/-- **The permutation of `Y_n` of `x ↦ δx + f`** (tex 401–402): `y ↦ σ_n(δ)y + ∑_h f(h) 1_{σ_n(h)}`. -/
noncomputable def modelAct (ξ : LampAffine Δ) : Equiv.Perm (ModelSpace M n) where
  toFun y := qSmul M n (M.σ n ξ.right) y + lampImage M n (Multiplicative.toAdd ξ.left)
  invFun y := qSmul M n (M.σ n ξ.right)⁻¹ (y - lampImage M n (Multiplicative.toAdd ξ.left))
  left_inv y := funext fun q' => by simp
  right_inv y := funext fun q' => by simp

theorem modelAct_apply (ξ : LampAffine Δ) (y : ModelSpace M n) :
    modelAct M n ξ y = qSmul M n (M.σ n ξ.right) y + lampImage M n (Multiplicative.toAdd ξ.left) :=
  rfl

theorem modelAct_one : modelAct M n 1 = 1 := by
  refine Equiv.ext fun y => ?_
  show qSmul M n (M.σ n 1) y + lampImage M n 0 = y
  rw [(M.isBallModel n).map_one, qSmul_one, lampImage_zero, add_zero]

/-- `inr δ` acts by `y ↦ σ_n(δ)y`. -/
theorem modelAct_inr (δ : Δ) (y : ModelSpace M n) :
    modelAct M n (SemidirectProduct.inr δ) y = qSmul M n (M.σ n δ) y := by
  show qSmul M n (M.σ n δ) y + lampImage M n 0 = _
  rw [lampImage_zero, add_zero]

/-- `z` acts by `y ↦ y + 1_e`. -/
theorem modelAct_lampAdd (y : ModelSpace M n) :
    modelAct M n (lampAdd Δ) y = y + Pi.single (1 : M.Q n) (1 : ZMod 2) := by
  show qSmul M n (M.σ n 1) y + lampImage M n (Finsupp.single 1 1) = _
  rw [(M.isBallModel n).map_one, qSmul_one, lampImage_single, (M.isBallModel n).map_one]

/-- **These permutations multiply as in `Λ`** (tex 404–405), for fixed elements and large `n`. -/
theorem eventually_modelAct_mul (hT : Subgroup.closure T = ⊤) (ξ η : LampAffine Δ) :
    ∀ᶠ n in atTop, modelAct M n (ξ * η) = modelAct M n ξ * modelAct M n η := by
  have hsupp : ∀ᶠ n in atTop, ∀ a ∈ (Multiplicative.toAdd η.left).support,
      M.σ n (ξ.right * a) = M.σ n ξ.right * M.σ n a :=
    (eventually_all_finset _).2 fun a _ => M.eventually_map_mul hT ξ.right a
  refine ((M.eventually_map_mul hT ξ.right η.right).and hsupp).mono fun n hn =>
    Equiv.ext fun y => ?_
  obtain ⟨hδ, hh⟩ := hn
  rw [Equiv.Perm.mul_apply, modelAct_apply, modelAct_apply, modelAct_apply]
  show qSmul M n (M.σ n (ξ.right * η.right)) y +
      lampImage M n (Multiplicative.toAdd ξ.left +
        translate Δ ξ.right (Multiplicative.toAdd η.left)) =
    qSmul M n (M.σ n ξ.right)
        (qSmul M n (M.σ n η.right) y + lampImage M n (Multiplicative.toAdd η.left)) +
      lampImage M n (Multiplicative.toAdd ξ.left)
  rw [hδ, lampImage_add, lampImage_translate M n hh, qSmul_add, qSmul_qSmul]
  abel

/-- The point `y ∘ σ_n` of `Ω` attached to `y` (tex 403–404). -/
def attach (y : ModelSpace M n) : LampSpace Δ :=
  fun h => y (M.σ n h)

/-- **The attached points move as `Λ` moves the points of `Ω`** (tex 405–406): for fixed `ξ`, a
finite set `J` and large `n`, `attach (ξ y)` and `ξ • attach y` agree on `J`, uniformly in `y`. -/
theorem eventually_attach_modelAct (hT : Subgroup.closure T = ⊤) (ξ : LampAffine Δ)
    (J : Finset Δ) :
    ∀ᶠ n in atTop, ∀ y : ModelSpace M n, ∀ h ∈ J,
      attach M n (modelAct M n ξ y) h = (ξ • attach M n y) h := by
  classical
  have h1 : ∀ᶠ n in atTop, ∀ h ∈ J,
      M.σ n (ξ.right⁻¹ * h) = (M.σ n ξ.right)⁻¹ * M.σ n h :=
    (eventually_all_finset J).2 fun h _ =>
      ((M.eventually_map_mul hT ξ.right⁻¹ h).and (M.eventually_map_inv hT ξ.right)).mono
        fun n hn => by rw [hn.1, hn.2]
  have h2 : ∀ᶠ n in atTop, ∀ h ∈ J, ∀ c ∈ (Multiplicative.toAdd ξ.left).support,
      h ≠ c → M.σ n h ≠ M.σ n c :=
    (eventually_all_finset J).2 fun h _ =>
      (eventually_all_finset (Multiplicative.toAdd ξ.left).support).2 fun c _ => by
        by_cases hhc : h = c
        · exact Eventually.of_forall fun _ hne => absurd hhc hne
        · exact (M.eventually_ne hT hhc).mono fun _ hne _ => hne
  refine (h1.and h2).mono fun n hn y h hJ => ?_
  obtain ⟨hn1, hn2⟩ := hn
  rw [smul_apply]
  show (modelAct M n ξ y) (M.σ n h) =
    y (M.σ n (ξ.right⁻¹ * h)) + Multiplicative.toAdd ξ.left h
  rw [modelAct_apply, Pi.add_apply, qSmul_apply, hn1 h hJ, lampImage_eq_sum_support,
    Finset.sum_apply]
  congr 1
  calc ∑ c ∈ (Multiplicative.toAdd ξ.left).support,
        (Pi.single (M.σ n c) (1 : ZMod 2) : ModelSpace M n) (M.σ n h)
      = ∑ c ∈ (Multiplicative.toAdd ξ.left).support, (if h = c then (1 : ZMod 2) else 0) :=
        Finset.sum_congr rfl fun c hc => by
          by_cases hhc : h = c
          · rw [if_pos hhc, hhc, Pi.single_eq_same]
          · rw [if_neg hhc, Pi.single_eq_of_ne (hn2 h hJ c hc hhc)]
    _ = if h ∈ (Multiplicative.toAdd ξ.left).support then 1 else 0 :=
        Finset.sum_ite_eq _ _ fun _ => (1 : ZMod 2)
    _ = Multiplicative.toAdd ξ.left h := by
        by_cases hs : h ∈ (Multiplicative.toAdd ξ.left).support
        · rw [if_pos hs]
          rcases zmod_two_eq_zero_or_one (Multiplicative.toAdd ξ.left h) with h0 | h1'
          · exact absurd h0 (Finsupp.mem_support_iff.1 hs)
          · exact h1'.symm
        · rw [if_neg hs, Finsupp.notMem_support_iff.1 hs]

end Lamplighter

open Lamplighter

/-- **The action on the finite models** (tex 401–406): for finite models `σ_n` of `Δ` on balls,
`x ↦ δx + f` acts on `Y_n` by `y ↦ σ_n(δ)y + ∑_{h ∈ supp f} 1_{σ_n(h)}`; for fixed elements of `Λ`
and large `n` these permutations multiply as in `Λ`; and uniformly in `y` they move the attached
points `y ∘ σ_n` near `e` as `Λ` moves the points of `Ω`. -/
def PrintedLamplighterModelAction : Prop :=
  ∀ (Δ : Type) [Group Δ] (T : Set Δ), Subgroup.closure T = ⊤ → ∀ M : BallModelSequence Δ T,
    (∀ (n : ℕ) (ξ : LampAffine Δ) (y : ModelSpace M n),
      modelAct M n ξ y = qSmul M n (M.σ n ξ.right) y +
        ∑ h ∈ (Multiplicative.toAdd ξ.left).support, Pi.single (M.σ n h) (1 : ZMod 2)) ∧
    (∀ ξ η : LampAffine Δ, ∀ᶠ n in Filter.atTop,
      modelAct M n (ξ * η) = modelAct M n ξ * modelAct M n η) ∧
    (∀ (ξ : LampAffine Δ) (J : Finset Δ), ∀ᶠ n in Filter.atTop, ∀ y : ModelSpace M n, ∀ h ∈ J,
      attach M n (modelAct M n ξ y) h = (ξ • attach M n y) h)

theorem printedLamplighterModelAction : PrintedLamplighterModelAction := fun _ _ _ hT M =>
  ⟨fun n ξ y => by rw [modelAct_apply, lampImage_eq_sum_support],
    fun ξ η => eventually_modelAct_mul M hT ξ η, fun ξ J => eventually_attach_modelAct M hT ξ J⟩

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLamplighterModelAction

end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.modelAct_lampAdd
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.modelAct_inr
