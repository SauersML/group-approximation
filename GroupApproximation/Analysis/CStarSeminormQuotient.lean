import GroupApproximation.Analysis.CStarTensorProductSeminorm
import Mathlib.Data.Real.Pointwise
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Real.Sqrt

/-!
# Star-stable ideals, quotients, and suprema of C⋆-seminorms

## Where this sits in the tensor-product lane

`CStarTensorProduct.lean` records the roadmap for the missing minimal tensor
product.  Stage A is done: the operator seminorm of a ⋆-representation is a
C⋆-seminorm (`StarRep.isCStarSeminorm`), a C⋆-norm when the representation is
faithful.  The two things the roadmap then names are

* a *canonical* norm, which the textbook route gets from Takesaki's
  independence theorem (Stage C, research scale), and for which the roadmap
  records a cheap alternative: *"define the minimal norm as a supremum over a
  set of representations manufactured from states.  The pointwise supremum of
  a bounded family of C⋆-seminorms is a C⋆-seminorm --- squaring is monotone
  on `[0, ∞)`, so the C⋆-identity survives the supremum --- so this is
  cheap."*  That sentence is `isCStarSeminorm_iSup` below, proved.
* quotients, which `CStarExactness.lean` lists among the things Mathlib does
  not have: *"`Mathlib/Analysis/Normed/Group/Quotient.lean` has
  `Ideal.Quotient.semiNormedCommRing` and `normedCommRing`, both commutative
  only; nothing makes `B ⧸ J` a C⋆-algebra."*

This file supplies the parts of both that are reachable at the pin, and is
explicit about the part that is not.

## What is proved here

* `IsStarStable` --- a two-sided ideal closed under the involution --- and the
  `Star`, `InvolutiveStar` and `StarRing` structures it induces on `A ⧸ I`.
  Mathlib has none of these: they are built here the same way
  `Analysis/NormMatrixCorona.lean` builds them for the matrix corona, by
  lifting the involution along `QuotientAddGroup.lift`.  This is the
  *algebraic* half of a C⋆-quotient and it is unconditional.
* `IsCStarSeminorm.comp` --- a C⋆-seminorm pulls back along a
  ⋆-homomorphism.
* `isCStarSeminorm_iSup` --- the pointwise supremum of a nonempty pointwise
  bounded family of C⋆-seminorms is a C⋆-seminorm.  The C⋆-identity is the
  only interesting field, and it is proved by `Real.sqrt` rather than by a
  monotone-image-of-a-supremum lemma, so nothing about continuity is needed.
* `IsCStarSeminorm.nullIdeal` --- the null set of a C⋆-seminorm is a two-sided
  star-stable ideal, and the seminorm is constant on its cosets.
* `exists_isCStarNorm_on_quotient` --- **the payoff**: every C⋆-seminorm on a
  complex ⋆-algebra descends to a genuine C⋆-*norm* on the quotient by its
  null ideal.  Combined with `isCStarSeminorm_iSup` and
  `StarRep.isCStarSeminorm`, an arbitrary nonempty bounded family of
  ⋆-representations of `A` now yields a C⋆-normed ⋆-algebra canonically
  attached to that family, with no faithfulness hypothesis on any member.

## What is *not* proved here, and why

**This is not the C⋆-quotient theorem.**  For a C⋆-algebra `B` and a closed
two-sided ideal `J`, the assertion that the *quotient norm*
`‖b + J‖ = inf {‖b + j‖ : j ∈ J}` satisfies the C⋆-identity is a genuine
theorem whose standard proof runs through an approximate unit of `J` and the
identity `‖b + J‖ = lim_λ ‖b - b e_λ‖`.  Nothing below proves it, and nothing
below is a substitute for it: the norms handled here are C⋆-seminorms *given
in advance*, and the descent to the quotient by the null ideal is the trivial
direction (the null ideal is exactly where the given seminorm already
vanishes, so no infimum is ever taken).  The pin does carry
`Mathlib/Analysis/CStarAlgebra/ApproximateUnit.lean`, so the quotient theorem
is not obviously out of reach, but it is not done here.  For the one quotient
this development needs it for — the tracial matrix quotient — it *is* now
done, through a bespoke approximate unit of its null ideal: the identity in
`Analysis/TracialQuotientCStarIdentity.lean`, the instances and the exact
norm formula in `Analysis/TracialQuotientCStar.lean`.  The theorem for a
general `B` and `J` remains unformalized.

Consequently the exactness rows of `non_mf_groups_exist.tex` (`SO.16`) and the
nuclearity row (`RE.05`) are untouched: exactness is defined through
`⊗_min`, whose canonicity is Takesaki's theorem, and through quotients in the
sense just excluded.

## Manuscript status

Infrastructure only; certifies no manuscript step.  `SO.16` and `RE.05` remain
**MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

universe u v

/-! ## Star-stable ideals and the involution on the quotient -/

/-- A two-sided ideal of a ⋆-ring that is closed under the involution.  This is
what is needed for the quotient ring to carry an involution; Mathlib has no
such class and no `StarRing` structure on any ring quotient. -/
class IsStarStable {A : Type u} [Ring A] [StarRing A] (I : Ideal A) : Prop where
  /-- The ideal is closed under the involution. -/
  star_mem : ∀ {a : A}, a ∈ I → star a ∈ I

section StarQuotient

variable {A : Type u} [Ring A] [StarRing A] (I : Ideal A) [I.IsTwoSided]
  [IsStarStable I]

private def quotientStarHom : A →+ A ⧸ I :=
  (Ideal.Quotient.mk I).toAddMonoidHom.comp starAddEquiv.toAddMonoidHom

private theorem toAddSubgroup_le_quotientStarHom_ker :
    I.toAddSubgroup ≤ (quotientStarHom I).ker := by
  intro a ha
  change Ideal.Quotient.mk I (star a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact IsStarStable.star_mem ha

/-- The involution descends to the quotient by a star-stable two-sided
ideal. -/
noncomputable instance quotientStar : Star (A ⧸ I) where
  star := QuotientAddGroup.lift I.toAddSubgroup (quotientStarHom I)
    (toAddSubgroup_le_quotientStarHom_ker I)

@[simp] theorem quotient_star_mk (a : A) :
    star (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a) :=
  QuotientAddGroup.lift_mk _ _ _

noncomputable instance quotientInvolutiveStar : InvolutiveStar (A ⧸ I) where
  star_involutive x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change star (star (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk I a
      rw [quotient_star_mk, quotient_star_mk, star_star]

/-- **The quotient of a ⋆-ring by a star-stable two-sided ideal is a
⋆-ring.** -/
noncomputable instance quotientStarRing : StarRing (A ⧸ I) where
  star_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk I (a + b)) =
          star (Ideal.Quotient.mk I a) + star (Ideal.Quotient.mk I b)
        rw [quotient_star_mk, quotient_star_mk, quotient_star_mk, star_add]
        rfl
  star_mul x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk I (a * b)) =
          star (Ideal.Quotient.mk I b) * star (Ideal.Quotient.mk I a)
        rw [quotient_star_mk, quotient_star_mk, quotient_star_mk]
        rw [show star (a * b) = star b * star a from StarMul.star_mul a b]
        rfl

end StarQuotient

section QuotientScalars

variable {A : Type u} [Ring A] [Algebra ℂ A] (I : Ideal A) [I.IsTwoSided]

/-- The quotient map is `ℂ`-linear.  Mathlib supplies the `ℂ`-algebra
structure on `A ⧸ I` (`Ideal.Quotient.algebra`) and the bundled `ℂ`-algebra
map `Ideal.Quotient.mkₐ`; this is the unbundled scalar law that the C⋆-seminorm
fields below need. -/
theorem quotient_mk_smul (c : ℂ) (a : A) :
    Ideal.Quotient.mk I (c • a) = c • Ideal.Quotient.mk I a :=
  map_smul (Ideal.Quotient.mkₐ ℂ I) c a

end QuotientScalars

/-! ## Pullback of a C⋆-seminorm -/

/-- **A C⋆-seminorm pulls back along a ⋆-homomorphism.**  With
`StarRep.isCStarSeminorm` this says that composing a representation with a
⋆-homomorphism again gives a C⋆-seminorm, which is the shape every
functoriality statement about tensor norms starts from. -/
theorem IsCStarSeminorm.comp {A : Type u} {B : Type v}
    [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]
    {p : B → ℝ} (hp : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B) :
    IsCStarSeminorm (fun a ↦ p (f a)) where
  nonneg a := hp.nonneg (f a)
  add_le a b := by simpa only [map_add] using hp.add_le (f a) (f b)
  smul c a := by simpa only [map_smul] using hp.smul c (f a)
  mul_le a b := by simpa only [map_mul] using hp.mul_le (f a) (f b)
  cstar a := by
    show p (f (star a * a)) = p (f a) * p (f a)
    -- `map_star` unqualified would resolve to `IsCStarSeminorm.map_star`
    -- (`p (star a) = p a`), because declaring `IsCStarSeminorm.comp` opens that
    -- namespace inside its own body; the mathlib lemma is reached through its
    -- class, since the root `map_star` is only an `export` alias.
    rw [map_mul f (star a) a, StarHomClass.map_star f a]
    exact hp.cstar (f a)

/-! ## Suprema of C⋆-seminorms

The roadmap in `CStarTensorProduct.lean` calls this "cheap"; it is, but the
C⋆-identity is not literally inherited from the members, because a supremum of
products is not a product of suprema.  What makes it work is that `t ↦ t²` is
an order isomorphism of `[0, ∞)`, and the cleanest way to use that without any
continuity lemma is to run the nontrivial inequality through `Real.sqrt`. -/

section Sup

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {ι : Type v}

/-- The pointwise supremum of a family of functions on `A`. -/
noncomputable def iSupSeminorm (p : ι → A → ℝ) : A → ℝ := fun a ↦ ⨆ i, p i a

omit [Ring A] [StarRing A] [Algebra ℂ A] in
@[simp] theorem iSupSeminorm_apply (p : ι → A → ℝ) (a : A) :
    iSupSeminorm p a = ⨆ i, p i a := rfl

/-- **The pointwise supremum of a bounded family of C⋆-seminorms is a
C⋆-seminorm.** -/
theorem isCStarSeminorm_iSup {p : ι → A → ℝ} (hne : Nonempty ι)
    (hp : ∀ i, IsCStarSeminorm (p i))
    (hb : ∀ a : A, BddAbove (Set.range fun i ↦ p i a)) :
    IsCStarSeminorm (iSupSeminorm p) where
  nonneg a :=
    le_ciSup_of_le (hb a) hne.some ((hp _).nonneg a)
  add_le a b := by
    refine ciSup_le fun i ↦ ?_
    exact ((hp i).add_le a b).trans
      (add_le_add (le_ciSup (hb a) i) (le_ciSup (hb b) i))
  smul c a := by
    show (⨆ i, p i (c • a)) = ‖c‖ * ⨆ i, p i a
    rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
    exact congrArg (fun f : ι → ℝ ↦ ⨆ i, f i)
      (funext fun i ↦ (hp i).smul c a)
  mul_le a b := by
    refine ciSup_le fun i ↦ ?_
    exact ((hp i).mul_le a b).trans
      (mul_le_mul (le_ciSup (hb a) i) (le_ciSup (hb b) i) ((hp i).nonneg b)
        (le_trans ((hp i).nonneg a) (le_ciSup (hb a) i)))
  cstar a := by
    have hnn : ∀ i, 0 ≤ p i a := fun i ↦ (hp i).nonneg a
    have hstar : ∀ i, p i (star a * a) = p i a * p i a := fun i ↦ (hp i).cstar a
    have hSA : (0 : ℝ) ≤ ⨆ i, p i a :=
      le_ciSup_of_le (hb a) (Classical.arbitrary ι) (hnn _)
    have hSG : (0 : ℝ) ≤ ⨆ i, p i (star a * a) :=
      le_ciSup_of_le (hb (star a * a)) (Classical.arbitrary ι)
        ((hp _).nonneg (star a * a))
    show (⨆ i, p i (star a * a)) = (⨆ i, p i a) * ⨆ i, p i a
    refine le_antisymm ?_ ?_
    · refine ciSup_le fun i ↦ ?_
      have hi : p i (star a * a) ≤ (⨆ i, p i a) * ⨆ i, p i a := by
        rw [hstar i]
        exact mul_le_mul (le_ciSup (hb a) i) (le_ciSup (hb a) i) (hnn i) hSA
      exact hi
    · have hle : (⨆ i, p i a) ≤ Real.sqrt (⨆ i, p i (star a * a)) := by
        refine ciSup_le fun i ↦ ?_
        have hsq : p i a ^ 2 ≤ ⨆ i, p i (star a * a) := by
          rw [sq, ← hstar i]
          exact le_ciSup (hb (star a * a)) i
        exact (Real.le_sqrt (hnn i) hSG).mpr hsq
      calc (⨆ i, p i a) * ⨆ i, p i a
          ≤ Real.sqrt (⨆ i, p i (star a * a)) *
              Real.sqrt (⨆ i, p i (star a * a)) :=
            mul_le_mul hle hle hSA (Real.sqrt_nonneg _)
        _ = ⨆ i, p i (star a * a) := Real.mul_self_sqrt hSG

/-- The supremum of a bounded family of ⋆-representation seminorms is a
C⋆-seminorm, with no faithfulness hypothesis on any member.  This is the
canonical-seminorm recipe the tensor roadmap names. -/
theorem isCStarSeminorm_iSup_starRep {V : ι → Type*}
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
    (hne : Nonempty ι) (π : ∀ i, StarRep A (V i))
    (hb : ∀ a : A, BddAbove (Set.range fun i ↦ (π i).seminorm a)) :
    IsCStarSeminorm (iSupSeminorm fun i ↦ (π i).seminorm) :=
  isCStarSeminorm_iSup hne (fun i ↦ (π i).isCStarSeminorm) hb

end Sup

/-! ## The null ideal, and the induced C⋆-norm on the quotient -/

namespace IsCStarSeminorm

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}

theorem map_neg (h : IsCStarSeminorm p) (a : A) : p (-a) = p a := by
  have h1 := h.smul (-1 : ℂ) a
  rw [neg_one_smul] at h1
  simpa using h1

/-- The null set of a C⋆-seminorm is an ideal. -/
def nullIdeal (h : IsCStarSeminorm p) : Ideal A where
  carrier := {a | p a = 0}
  zero_mem' := h.map_zero
  add_mem' := by
    intro a b ha hb
    have ha' : p a = 0 := ha
    have hb' : p b = 0 := hb
    have hab : p (a + b) ≤ p a + p b := h.add_le a b
    rw [ha', hb', add_zero] at hab
    exact le_antisymm hab (h.nonneg _)
  smul_mem' := by
    intro c a ha
    have ha' : p a = 0 := ha
    have hca : p (c * a) ≤ p c * p a := h.mul_le c a
    rw [ha', mul_zero] at hca
    show p (c • a) = 0
    rw [smul_eq_mul]
    exact le_antisymm hca (h.nonneg _)

theorem mem_nullIdeal_iff (h : IsCStarSeminorm p) (a : A) :
    a ∈ h.nullIdeal ↔ p a = 0 := Iff.rfl

instance nullIdeal_isTwoSided (h : IsCStarSeminorm p) :
    (h.nullIdeal).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    have ha' : p a = 0 := ha
    have hab : p (a * b) ≤ p a * p b := h.mul_le a b
    rw [ha', zero_mul] at hab
    exact le_antisymm hab (h.nonneg _)

instance nullIdeal_isStarStable (h : IsCStarSeminorm p) :
    IsStarStable (h.nullIdeal) where
  star_mem := by
    intro a ha
    have ha' : p a = 0 := ha
    show p (star a) = 0
    rw [h.map_star]
    exact ha'

/-- A C⋆-seminorm is constant on the cosets of its null ideal. -/
theorem eq_of_sub_mem_nullIdeal (h : IsCStarSeminorm p) {a b : A}
    (hab : a - b ∈ h.nullIdeal) : p a = p b := by
  have h0 : p (a - b) = 0 := hab
  have hba : p (b - a) = 0 := by
    have hneg := h.map_neg (a - b)
    rw [neg_sub, h0] at hneg
    exact hneg
  have h1 : p a ≤ p b := by
    have hb := h.add_le b (a - b)
    rw [(show b + (a - b) = a by abel), h0, add_zero] at hb
    exact hb
  have h2 : p b ≤ p a := by
    have ha := h.add_le a (b - a)
    rw [(show a + (b - a) = b by abel), hba, add_zero] at ha
    exact ha
  exact le_antisymm h1 h2

/-- **Every C⋆-seminorm descends to a C⋆-norm on the quotient by its null
ideal.**

The quotient carries Mathlib's ring and `ℂ`-algebra structures and the
involution built in this file, so the statement is about a genuine complex
⋆-algebra.  No infimum is taken anywhere: the descended function agrees with
`p` on every representative, which is the first conjunct.

This is *not* the C⋆-quotient theorem for a closed ideal of a C⋆-algebra; see
the module docstring. -/
theorem exists_isCStarNorm_on_quotient (h : IsCStarSeminorm p) :
    ∃ q : (A ⧸ h.nullIdeal) → ℝ,
      (∀ a : A, q (Ideal.Quotient.mk h.nullIdeal a) = p a) ∧ IsCStarNorm q := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : (A ⧸ h.nullIdeal) → A,
      ∀ x, Ideal.Quotient.mk h.nullIdeal (g x) = x :=
    ⟨fun x ↦ Classical.choose (Ideal.Quotient.mk_surjective x),
      fun x ↦ Classical.choose_spec (Ideal.Quotient.mk_surjective x)⟩
  have hkey : ∀ a : A, p (g (Ideal.Quotient.mk h.nullIdeal a)) = p a := by
    intro a
    apply h.eq_of_sub_mem_nullIdeal
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hg _
  refine ⟨fun x ↦ p (g x), hkey, ?_, ?_⟩
  · refine ⟨fun x ↦ h.nonneg (g x), ?_, ?_, ?_, ?_⟩
    · intro x y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_add]
      simp only [hkey]
      exact h.add_le a b
    · intro c x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← quotient_mk_smul]
      simp only [hkey]
      exact h.smul c a
    · intro x y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul]
      simp only [hkey]
      exact h.mul_le a b
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [quotient_star_mk, ← map_mul]
      simp only [hkey]
      exact h.cstar a
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [hkey] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hx

/-- **The C⋆-norm the seminorm induces on the quotient by its null ideal**, as a
named function rather than an existential witness.

`exists_isCStarNorm_on_quotient` produces it existentially, which is enough to
know the quotient is C⋆-normable but not enough to *norm* it: installing a norm
as an instance requires naming the function, since the type synonym that carries
it is indexed by the proof that this particular function is a C⋆-norm.  The
choice is therefore made once, here, and every later statement about the
enveloping algebra of `p` refers back to it. -/
noncomputable def quotientNorm (h : IsCStarSeminorm p) : (A ⧸ h.nullIdeal) → ℝ :=
  Classical.choose h.exists_isCStarNorm_on_quotient

/-- The induced norm computes the seminorm on every representative.  In
particular it takes no infimum: see the module docstring. -/
@[simp] theorem quotientNorm_mk (h : IsCStarSeminorm p) (a : A) :
    h.quotientNorm (Ideal.Quotient.mk h.nullIdeal a) = p a :=
  (Classical.choose_spec h.exists_isCStarNorm_on_quotient).1 a

theorem isCStarNorm_quotientNorm (h : IsCStarSeminorm p) :
    IsCStarNorm h.quotientNorm :=
  (Classical.choose_spec h.exists_isCStarNorm_on_quotient).2

end IsCStarSeminorm

end CStarTensor
end GroupApproximation
