import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureBasic
import GroupApproximation.KirchbergAlgebra.MinTensorSeparable
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-!
# The minimal tensor product of separable non-unital C⋆-algebras

The bootstrap class of Rosenberg--Schochet (Duke Math. J. 55 (1987), §2) is closed under minimal
tensor products, via Kasparov's external product (Blackadar, *K-Theory for Operator Algebras*,
18.9).  This file supplies the object part for non-unital algebras.

The repository's minimal tensor product `CStarTensor.MinTensorProduct` is built for unital
algebras.  For non-unital `A` and `C` we form it for the unitizations `A⁺` and `C⁺` and take the
norm closure of the span of the elementary tensors `a ⊗ c`, with `a ∈ A` and `c ∈ C`:

* `MinTensor.gen a c`: the elementary tensor `a ⊗ c` in `A⁺ ⊗_min C⁺`, with `gen_mul_gen` and
  `star_gen`;
* `MinTensor.preAlgebra`: the span of the elementary tensors, a `⋆`-subalgebra;
* `MinTensor.closed`: its norm closure, a non-unital C⋆-algebra that is separable when `A` and `C`
  are;
* `SepNUCStarAlgebra.minTensor A C`: the bundled algebra `A ⊗_min C`;
* `SepNUCStarAlgebra.IsCommutative.minTensor`: a minimal tensor product of commutative algebras is
  commutative.

Functoriality in both variables is in `BootstrapMinTensorMap`.

Manuscript: `non_mf_group_notes.tex`, UCT input of `thm:fixed-radical-membership`
(lane TWWUCT-F3, work order WO-TWWUCT-F-3).
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.CStarTensor
open scoped TensorProduct

noncomputable section

namespace MinTensor

variable (A C : Type) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

/-- The ambient unital algebra `A⁺ ⊗_min C⁺`. -/
abbrev Ambient : Type :=
  MinTensorProduct (Unitization ℂ A) (Unitization ℂ C)

/-- The elementary tensor `a ⊗ c ∈ A⁺ ⊗_min C⁺` of `a ∈ A` and `c ∈ C`. -/
def gen (a : A) (c : C) : Ambient A C :=
  minTensorIn (Unitization ℂ A) (Unitization ℂ C)
    ((Unitization.inr a : Unitization ℂ A) ⊗ₜ[ℂ] (Unitization.inr c : Unitization ℂ C))

/-- The elementary tensors of `A` and `C`. -/
abbrev generators : Set (Ambient A C) :=
  Set.range fun p : A × C => gen A C p.1 p.2

variable {A C}

/-- Elementary tensors multiply leg by leg. -/
theorem gen_mul_gen (a a' : A) (c c' : C) :
    gen A C a c * gen A C a' c' = gen A C (a * a') (c * c') := by
  rw [gen, gen, gen, ← map_mul (minTensorIn (Unitization ℂ A) (Unitization ℂ C)),
    Algebra.TensorProduct.tmul_mul_tmul, Unitization.inr_mul, Unitization.inr_mul]

/-- The adjoint of an elementary tensor. -/
theorem star_gen (a : A) (c : C) : star (gen A C a c) = gen A C (star a) (star c) := by
  rw [gen, gen, ← map_star (minTensorIn (Unitization ℂ A) (Unitization ℂ C)),
    TensorProduct.star_tmul, Unitization.inr_star, Unitization.inr_star]

/-- The span of the elementary tensors is closed under multiplication. -/
theorem span_mul_mem {x y : Ambient A C} (hx : x ∈ Submodule.span ℂ (generators A C))
    (hy : y ∈ Submodule.span ℂ (generators A C)) :
    x * y ∈ Submodule.span ℂ (generators A C) := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨p, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨q, rfl⟩ := hy'
      show gen A C p.1 p.2 * gen A C q.1 q.2 ∈ Submodule.span ℂ (generators A C)
      rw [gen_mul_gen]
      exact Submodule.subset_span ⟨(p.1 * q.1, p.2 * q.2), rfl⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [mul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hy
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x z _ _ hx hz =>
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  | smul r x _ hx =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hx

/-- The span of the elementary tensors is closed under the adjoint. -/
theorem span_star_mem {x : Ambient A C} (hx : x ∈ Submodule.span ℂ (generators A C)) :
    star x ∈ Submodule.span ℂ (generators A C) := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨p, rfl⟩ := hx'
    show star (gen A C p.1 p.2) ∈ Submodule.span ℂ (generators A C)
    rw [star_gen]
    exact Submodule.subset_span ⟨(star p.1, star p.2), rfl⟩
  | zero =>
    rw [star_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [star_smul]
    exact Submodule.smul_mem _ (star r) hx

variable (A C)

/-- The `⋆`-algebra spanned by the elementary tensors `a ⊗ c`, `a ∈ A`, `c ∈ C`. -/
def preAlgebra : NonUnitalStarSubalgebra ℂ (Ambient A C) :=
  { (Submodule.span ℂ (generators A C)).toNonUnitalSubalgebra
      (fun _ _ hx hy => span_mul_mem hx hy) with
    star_mem' := fun hx => span_star_mem hx }

/-- **The minimal tensor product `A ⊗_min C`** of non-unital algebras: the norm closure of the
elementary tensors inside `A⁺ ⊗_min C⁺`. -/
def closed : NonUnitalStarSubalgebra ℂ (Ambient A C) :=
  (preAlgebra A C).topologicalClosure

instance isClosed_closed : IsClosed (closed A C : Set (Ambient A C)) :=
  (preAlgebra A C).isClosed_topologicalClosure

noncomputable instance instNonUnitalCStarAlgebraClosed : NonUnitalCStarAlgebra (closed A C) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (closed A C)

variable {A C}

theorem mem_preAlgebra {x : Ambient A C} :
    x ∈ preAlgebra A C ↔ x ∈ Submodule.span ℂ (generators A C) :=
  Iff.rfl

theorem mem_closed {x : Ambient A C} :
    x ∈ closed A C ↔ x ∈ closure (Submodule.span ℂ (generators A C) : Set (Ambient A C)) :=
  Iff.rfl

/-- The elementary tensors lie in `A ⊗_min C`. -/
theorem gen_mem_closed (a : A) (c : C) : gen A C a c ∈ closed A C :=
  mem_closed.2 (subset_closure (Submodule.subset_span ⟨(a, c), rfl⟩))

/-- The elementary tensor `a ⊗ c` as an element of `A ⊗_min C`. -/
def tmul (a : A) (c : C) : closed A C :=
  ⟨gen A C a c, gen_mem_closed a c⟩

@[simp] theorem coe_tmul (a : A) (c : C) : (tmul a c : Ambient A C) = gen A C a c :=
  rfl

variable (A C)

/-- The elementary tensor map `A × C → A⁺ ⊗_min C⁺` is continuous. -/
theorem continuous_gen : Continuous fun p : A × C => gen A C p.1 p.2 := by
  have h1 : Continuous fun p : Unitization ℂ A × Unitization ℂ C =>
      minTensorIn (Unitization ℂ A) (Unitization ℂ C) (p.1 ⊗ₜ[ℂ] p.2) :=
    GroupApproximation.KirchbergAlgebra.continuous_minTensorIn_tmul
  have h2 : Continuous fun p : A × C =>
      ((Unitization.inr p.1 : Unitization ℂ A), (Unitization.inr p.2 : Unitization ℂ C)) :=
    ((Unitization.continuous_inr (𝕜 := ℂ)).comp continuous_fst).prodMk
      ((Unitization.continuous_inr (𝕜 := ℂ)).comp continuous_snd)
  exact h1.comp h2

variable {A C}

/-- **Separability**: `A ⊗_min C` is separable when `A` and `C` are. -/
instance separableSpace_closed [TopologicalSpace.SeparableSpace A]
    [TopologicalSpace.SeparableSpace C] : TopologicalSpace.SeparableSpace (closed A C) := by
  have hT : _root_.TopologicalSpace.IsSeparable
      (Set.range fun p : A × C => gen A C p.1 p.2) := by
    rw [← Set.image_univ]
    exact (_root_.TopologicalSpace.isSeparable_univ_iff.2 inferInstance).image
      (continuous_gen A C)
  have hS : _root_.TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (generators A C) : Set (Ambient A C))) :=
    _root_.TopologicalSpace.isSeparable_closure.2
      (_root_.TopologicalSpace.IsSeparable.span (R := ℂ) hT)
  have hS' : _root_.TopologicalSpace.IsSeparable (closed A C : Set (Ambient A C)) := hS
  exact hS'.separableSpace

/-! ## Commutativity -/

/-- Elementary tensors of commutative algebras commute, hence so does their span. -/
theorem span_comm (hA : ∀ x y : A, x * y = y * x) (hC : ∀ x y : C, x * y = y * x)
    {x y : Ambient A C} (hx : x ∈ Submodule.span ℂ (generators A C))
    (hy : y ∈ Submodule.span ℂ (generators A C)) : x * y = y * x := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨p, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨q, rfl⟩ := hy'
      show gen A C p.1 p.2 * gen A C q.1 q.2 = gen A C q.1 q.2 * gen A C p.1 p.2
      rw [gen_mul_gen, gen_mul_gen, hA p.1 q.1, hC p.2 q.2]
    | zero => rw [mul_zero, zero_mul]
    | add y z _ _ hy hz => rw [mul_add, add_mul, hy, hz]
    | smul r y _ hy => rw [mul_smul_comm, smul_mul_assoc, hy]
  | zero => rw [zero_mul, mul_zero]
  | add x z _ _ hx hz => rw [add_mul, mul_add, hx, hz]
  | smul r x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/-- Commutation passes to the norm closure. -/
theorem closure_comm (hA : ∀ x y : A, x * y = y * x) (hC : ∀ x y : C, x * y = y * x)
    {x y : Ambient A C}
    (hx : x ∈ closure (Submodule.span ℂ (generators A C) : Set (Ambient A C)))
    (hy : y ∈ closure (Submodule.span ℂ (generators A C) : Set (Ambient A C))) :
    x * y = y * x := by
  have h1 : ∀ v ∈ (Submodule.span ℂ (generators A C) : Set (Ambient A C)),
      ∀ u ∈ closure (Submodule.span ℂ (generators A C) : Set (Ambient A C)),
        u * v = v * u := by
    intro v hv u hu
    have hcl : IsClosed {w : Ambient A C | w * v = v * w} :=
      isClosed_eq (continuous_mul_const v) (continuous_const_mul v)
    have hsub : (Submodule.span ℂ (generators A C) : Set (Ambient A C)) ⊆
        {w : Ambient A C | w * v = v * w} := by
      intro w hw
      exact span_comm hA hC hw hv
    exact closure_minimal hsub hcl hu
  have hcl : IsClosed {w : Ambient A C | x * w = w * x} :=
    isClosed_eq (continuous_const_mul x) (continuous_mul_const x)
  have hsub : (Submodule.span ℂ (generators A C) : Set (Ambient A C)) ⊆
      {w : Ambient A C | x * w = w * x} := by
    intro w hw
    exact h1 w hw x hx
  exact closure_minimal hsub hcl hy

/-- `A ⊗_min C` is commutative when `A` and `C` are. -/
theorem closed_comm (hA : ∀ x y : A, x * y = y * x) (hC : ∀ x y : C, x * y = y * x)
    (x y : closed A C) : x * y = y * x :=
  Subtype.ext (closure_comm hA hC (mem_closed.1 x.2) (mem_closed.1 y.2))

end MinTensor

/-- **The minimal tensor product** `A ⊗_min C` of separable non-unital C⋆-algebras. -/
def SepNUCStarAlgebra.minTensor (A C : SepNUCStarAlgebra) : SepNUCStarAlgebra where
  carrier := MinTensor.closed A C

/-- **A minimal tensor product of commutative algebras is commutative.** -/
theorem SepNUCStarAlgebra.IsCommutative.minTensor {A C : SepNUCStarAlgebra}
    (hA : A.IsCommutative) (hC : C.IsCommutative) : (A.minTensor C).IsCommutative :=
  fun x y => MinTensor.closed_comm (A := A) (C := C) hA hC x y

end

end GroupApproximation.Full.TWWUCT.Bootstrap
