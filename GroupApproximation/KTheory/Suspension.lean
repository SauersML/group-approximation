import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

/-!
# The cone and the suspension of a C*-algebra

For a C*-algebra `A` put `I = [0,1]` and

    CA = { f ∈ C(I, A) | f 0 = 0 },        SA = { f ∈ C(I, A) | f 0 = 0 and f 1 = 0 }.

Both are closed non-unital star subalgebras of the C*-algebra `C(I, A)`, hence C*-algebras, and
they sit in the short exact sequence

    0 → SA → CA → A → 0,

the second map being evaluation at `1`.  The cone is contractible: `f ↦ (t ↦ f (s t))` joins the
identity (`s = 1`) to the zero map (`s = 0`).  Everything is functorial in star homomorphisms.

This is the extension whose index map gives `K_1(A) ≅ K_0(SA)`
(Rørdam–Larsen–Laustsen, *An Introduction to K-Theory for C*-Algebras*, Chapter 10;
Blackadar, *K-Theory for Operator Algebras*, Section 8.2).

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace KTheory

open unitInterval

universe u v w

noncomputable section

section Defs

variable (A : Type u) [NonUnitalCStarAlgebra A]

/-- The cone `CA`: continuous paths `[0,1] → A` starting at `0`. -/
def cone : NonUnitalStarSubalgebra ℂ C(I, A) where
  carrier := {f | f 0 = 0}
  add_mem' := fun {f g} (hf : f 0 = 0) (hg : g 0 = 0) =>
    show f 0 + g 0 = 0 by rw [hf, hg, add_zero]
  zero_mem' := rfl
  mul_mem' := fun {f g} (hf : f 0 = 0) (_ : g 0 = 0) =>
    show f 0 * g 0 = 0 by rw [hf, zero_mul]
  smul_mem' := fun c {f} (hf : f 0 = 0) => show c • f 0 = 0 by rw [hf, smul_zero]
  star_mem' := fun {f} (hf : f 0 = 0) => show star (f 0) = 0 by rw [hf, star_zero]

/-- The suspension `SA`: continuous loops `[0,1] → A` based at `0`. -/
def suspension : NonUnitalStarSubalgebra ℂ C(I, A) where
  carrier := {f | f 0 = 0 ∧ f 1 = 0}
  add_mem' := fun {f g} (hf : f 0 = 0 ∧ f 1 = 0) (hg : g 0 = 0 ∧ g 1 = 0) =>
    show f 0 + g 0 = 0 ∧ f 1 + g 1 = 0 from
      ⟨by rw [hf.1, hg.1, add_zero], by rw [hf.2, hg.2, add_zero]⟩
  zero_mem' := ⟨rfl, rfl⟩
  mul_mem' := fun {f g} (hf : f 0 = 0 ∧ f 1 = 0) (_ : g 0 = 0 ∧ g 1 = 0) =>
    show f 0 * g 0 = 0 ∧ f 1 * g 1 = 0 from
      ⟨by rw [hf.1, zero_mul], by rw [hf.2, zero_mul]⟩
  smul_mem' := fun c {f} (hf : f 0 = 0 ∧ f 1 = 0) =>
    show c • f 0 = 0 ∧ c • f 1 = 0 from ⟨by rw [hf.1, smul_zero], by rw [hf.2, smul_zero]⟩
  star_mem' := fun {f} (hf : f 0 = 0 ∧ f 1 = 0) =>
    show star (f 0) = 0 ∧ star (f 1) = 0 from ⟨by rw [hf.1, star_zero], by rw [hf.2, star_zero]⟩

theorem mem_cone {f : C(I, A)} : f ∈ cone A ↔ f 0 = 0 := Iff.rfl

theorem mem_suspension {f : C(I, A)} : f ∈ suspension A ↔ f 0 = 0 ∧ f 1 = 0 := Iff.rfl

instance isClosed_cone : IsClosed (cone A : Set C(I, A)) :=
  isClosed_eq (continuous_eval_const (0 : I)) continuous_const

instance isClosed_suspension : IsClosed (suspension A : Set C(I, A)) :=
  (isClosed_eq (continuous_eval_const (0 : I)) continuous_const).inter
    (isClosed_eq (continuous_eval_const (1 : I)) continuous_const)

/-- The cone as a C*-algebra. -/
abbrev Cone : Type u := cone A

/-- The suspension as a C*-algebra. -/
abbrev Suspension : Type u := suspension A

instance instNonUnitalCStarAlgebraCone : NonUnitalCStarAlgebra (Cone A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (cone A)

instance instNonUnitalCStarAlgebraSuspension : NonUnitalCStarAlgebra (Suspension A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (suspension A)

variable {A} in
theorem Cone.apply_zero (f : Cone A) : (f : C(I, A)) 0 = 0 := f.2

variable {A} in
theorem Suspension.apply_zero (f : Suspension A) : (f : C(I, A)) 0 = 0 := f.2.1

variable {A} in
theorem Suspension.apply_one (f : Suspension A) : (f : C(I, A)) 1 = 0 := f.2.2

theorem suspension_le_cone : suspension A ≤ cone A := fun _ hf => And.left hf

/-- The inclusion `SA → CA`. -/
def Suspension.toCone : Suspension A →⋆ₙₐ[ℂ] Cone A :=
  NonUnitalStarSubalgebra.inclusion (suspension_le_cone A)

@[simp]
theorem Suspension.coe_toCone (f : Suspension A) :
    ((Suspension.toCone A f : Cone A) : C(I, A)) = f := rfl

theorem Suspension.toCone_injective : Function.Injective (Suspension.toCone A) :=
  fun _ _ h => Subtype.ext (congrArg (fun g : Cone A => (g : C(I, A))) h)

/-- Evaluation at the free end, `CA → A`. -/
def Cone.eval : Cone A →⋆ₙₐ[ℂ] A where
  toFun f := (f : C(I, A)) 1
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem Cone.eval_apply (f : Cone A) : Cone.eval A f = (f : C(I, A)) 1 := rfl

/-- The straight path `t ↦ t a` from `0` to `a`. -/
def Cone.ray (a : A) : Cone A :=
  ⟨⟨fun t => ((t : ℝ) : ℂ) • a,
      (Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const⟩,
    show ((0 : ℝ) : ℂ) • a = 0 by rw [Complex.ofReal_zero, zero_smul]⟩

theorem Cone.eval_ray (a : A) : Cone.eval A (Cone.ray A a) = a :=
  show ((1 : ℝ) : ℂ) • a = a by rw [Complex.ofReal_one, one_smul]

theorem Cone.eval_surjective : Function.Surjective (Cone.eval A) :=
  fun a => ⟨Cone.ray A a, Cone.eval_ray A a⟩

/-- Exactness in the middle: the kernel of evaluation is the suspension. -/
theorem Cone.eval_eq_zero_iff (f : Cone A) :
    Cone.eval A f = 0 ↔ (f : C(I, A)) ∈ suspension A :=
  ⟨fun h => ⟨f.2, h⟩, fun h => h.2⟩

theorem Cone.eval_toCone (f : Suspension A) : Cone.eval A (Suspension.toCone A f) = 0 :=
  Suspension.apply_one f

/-- Exactness in the middle, as a range statement. -/
theorem Cone.eval_eq_zero_iff_exists (f : Cone A) :
    Cone.eval A f = 0 ↔ ∃ g : Suspension A, Suspension.toCone A g = f := by
  refine ⟨fun h => ⟨⟨f, (Cone.eval_eq_zero_iff A f).mp h⟩, rfl⟩, ?_⟩
  rintro ⟨g, rfl⟩
  exact Cone.eval_toCone A g

end Defs

section Contraction

/-- Multiplication by `s` on the unit interval. -/
def scaleI (s : I) : C(I, I) :=
  ⟨fun t => ⟨(s : ℝ) * t, unitInterval.mul_mem s.2 t.2⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk fun t => unitInterval.mul_mem s.2 t.2⟩

theorem scaleI_apply_zero (s : I) : scaleI s 0 = 0 := Subtype.ext (mul_zero (s : ℝ))

theorem scaleI_one_apply (t : I) : scaleI 1 t = t := Subtype.ext (one_mul (t : ℝ))

theorem scaleI_zero_apply (t : I) : scaleI 0 t = 0 := Subtype.ext (zero_mul (t : ℝ))

theorem continuous_scaleI_uncurry : Continuous fun p : I × I => scaleI p.1 p.2 :=
  Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)) fun p => unitInterval.mul_mem p.1.2 p.2.2

variable (A : Type u) [NonUnitalCStarAlgebra A]

/-- The contraction of the cone, `f ↦ (t ↦ f (s t))`. -/
def Cone.contract (s : I) : Cone A →⋆ₙₐ[ℂ] Cone A where
  toFun f := ⟨(f : C(I, A)).comp (scaleI s),
    show (f : C(I, A)) (scaleI s 0) = 0 by rw [scaleI_apply_zero]; exact Cone.apply_zero f⟩
  map_smul' _ _ := Subtype.ext (ContinuousMap.ext fun _ => rfl)
  map_zero' := Subtype.ext (ContinuousMap.ext fun _ => rfl)
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (ContinuousMap.ext fun _ => rfl)
  map_star' _ := Subtype.ext (ContinuousMap.ext fun _ => rfl)

@[simp]
theorem Cone.contract_apply (s : I) (f : Cone A) (t : I) :
    ((Cone.contract A s f : Cone A) : C(I, A)) t = (f : C(I, A)) (scaleI s t) := rfl

theorem Cone.contract_one : Cone.contract A 1 = NonUnitalStarAlgHom.id ℂ (Cone A) :=
  NonUnitalStarAlgHom.ext fun f => Subtype.ext (ContinuousMap.ext fun t =>
    congrArg (fun x : I => (f : C(I, A)) x) (scaleI_one_apply t))

theorem Cone.contract_zero_apply (f : Cone A) : Cone.contract A 0 f = 0 :=
  Subtype.ext (ContinuousMap.ext fun t =>
    (congrArg (fun x : I => (f : C(I, A)) x) (scaleI_zero_apply t)).trans (Cone.apply_zero f))

/-- The contraction is a continuous path in `C(I, A)` for each point of the cone. -/
theorem Cone.continuous_contract (f : Cone A) :
    Continuous fun s : I => ((Cone.contract A s f : Cone A) : C(I, A)) := by
  let g : C(I × I, A) :=
    ⟨fun p => (f : C(I, A)) (scaleI p.1 p.2), (f : C(I, A)).continuous.comp continuous_scaleI_uncurry⟩
  exact (ContinuousMap.curry g).continuous.congr fun s => ContinuousMap.ext fun t => rfl

end Contraction

section Functorial

variable {A : Type u} [NonUnitalCStarAlgebra A] {B : Type v} [NonUnitalCStarAlgebra B]
  {C : Type w} [NonUnitalCStarAlgebra C]

/-- Star homomorphisms between C*-algebras are continuous. -/
theorem continuous_nonUnitalStarAlgHom (φ : A →⋆ₙₐ[ℂ] B) : Continuous φ :=
  AddMonoidHomClass.continuous_of_bound φ 1 fun a => by
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a

/-- Post-composition `C(I, A) → C(I, B)` with a star homomorphism. -/
def postcomp (φ : A →⋆ₙₐ[ℂ] B) : C(I, A) →⋆ₙₐ[ℂ] C(I, B) where
  toFun f := ⟨fun t => φ (f t), (continuous_nonUnitalStarAlgHom φ).comp f.continuous⟩
  map_smul' c f := ContinuousMap.ext fun t => map_smul φ c (f t)
  map_zero' := ContinuousMap.ext fun _ => map_zero φ
  map_add' f g := ContinuousMap.ext fun t => map_add φ (f t) (g t)
  map_mul' f g := ContinuousMap.ext fun t => map_mul φ (f t) (g t)
  map_star' f := ContinuousMap.ext fun t => map_star φ (f t)

@[simp]
theorem postcomp_apply (φ : A →⋆ₙₐ[ℂ] B) (f : C(I, A)) (t : I) : postcomp φ f t = φ (f t) := rfl

/-- The cone is a functor. -/
def Cone.map (φ : A →⋆ₙₐ[ℂ] B) : Cone A →⋆ₙₐ[ℂ] Cone B where
  toFun f := ⟨postcomp φ f, show φ ((f : C(I, A)) 0) = 0 by rw [Cone.apply_zero f, map_zero]⟩
  map_smul' c f := Subtype.ext (map_smul (postcomp φ) c (f : C(I, A)))
  map_zero' := Subtype.ext (map_zero (postcomp φ))
  map_add' f g := Subtype.ext (map_add (postcomp φ) (f : C(I, A)) g)
  map_mul' f g := Subtype.ext (map_mul (postcomp φ) (f : C(I, A)) g)
  map_star' f := Subtype.ext (map_star (postcomp φ) (f : C(I, A)))

/-- The suspension is a functor. -/
def Suspension.map (φ : A →⋆ₙₐ[ℂ] B) : Suspension A →⋆ₙₐ[ℂ] Suspension B where
  toFun f := ⟨postcomp φ f, show φ ((f : C(I, A)) 0) = 0 ∧ φ ((f : C(I, A)) 1) = 0 from
    ⟨by rw [Suspension.apply_zero f, map_zero], by rw [Suspension.apply_one f, map_zero]⟩⟩
  map_smul' c f := Subtype.ext (map_smul (postcomp φ) c (f : C(I, A)))
  map_zero' := Subtype.ext (map_zero (postcomp φ))
  map_add' f g := Subtype.ext (map_add (postcomp φ) (f : C(I, A)) g)
  map_mul' f g := Subtype.ext (map_mul (postcomp φ) (f : C(I, A)) g)
  map_star' f := Subtype.ext (map_star (postcomp φ) (f : C(I, A)))

@[simp]
theorem Cone.coe_map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : Cone A) (t : I) :
    ((Cone.map φ f : Cone B) : C(I, B)) t = φ ((f : C(I, A)) t) := rfl

@[simp]
theorem Suspension.coe_map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : Suspension A) (t : I) :
    ((Suspension.map φ f : Suspension B) : C(I, B)) t = φ ((f : C(I, A)) t) := rfl

theorem Cone.map_id : Cone.map (NonUnitalStarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (Cone A) :=
  NonUnitalStarAlgHom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => rfl)

theorem Suspension.map_id :
    Suspension.map (NonUnitalStarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (Suspension A) :=
  NonUnitalStarAlgHom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => rfl)

theorem Cone.map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    Cone.map (ψ.comp φ) = (Cone.map ψ).comp (Cone.map φ) :=
  NonUnitalStarAlgHom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => rfl)

theorem Suspension.map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    Suspension.map (ψ.comp φ) = (Suspension.map ψ).comp (Suspension.map φ) :=
  NonUnitalStarAlgHom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => rfl)

/-- Evaluation is natural. -/
theorem Cone.eval_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    (Cone.eval B).comp (Cone.map φ) = φ.comp (Cone.eval A) :=
  NonUnitalStarAlgHom.ext fun _ => rfl

/-- The inclusion of the suspension in the cone is natural. -/
theorem Suspension.toCone_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    (Suspension.toCone B).comp (Suspension.map φ) = (Cone.map φ).comp (Suspension.toCone A) :=
  NonUnitalStarAlgHom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => rfl)

end Functorial

end

end KTheory
end GroupApproximation
