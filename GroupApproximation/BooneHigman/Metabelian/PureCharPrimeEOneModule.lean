import Mathlib.Algebra.Module.ZMod
import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RingTheory.Finiteness.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# The base of an exponent-`p` split extension as an `F_p[Q]`-module (bh-met-26)

For a commutative group `B` with `b ^ p = 1` and `φ : Q →* MulAut B`, the type synonym
`EOneMod φ p hV := Additive B` carries a `ZMod p`-module structure, the representation
`eOneRep` of `Q` induced by `φ`, and hence an `F_p[Q]`-module structure (`Module.compHom` along
`Representation.asAlgebraHom`).  The action of a group element is `φ` itself (`eOne_smul`).
If `B ⋊[φ] Q` is finitely generated, the module is finite (`eOne_finite`): the left
components of a finite generating set span a submodule whose preimage is a subgroup containing
the generators.

The synonym carries `φ`, `p` and `hV` in its type, so that instance resolution finds the module
structures without `letI`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

section EOneModule

variable {B Q : Type} [CommGroup B] [Group Q]

/-- Type synonym for `Additive B`, carrying the `F_p[Q]`-module structure induced by `φ`. -/
def EOneMod (_φ : Q →* MulAut B) (p : ℕ) (_hV : ∀ b : B, b ^ p = 1) : Type := Additive B

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.EOneMod

variable {φ : Q →* MulAut B} {p : ℕ} {hV : ∀ b : B, b ^ p = 1}

instance instAddCommGroupEOneMod : AddCommGroup (EOneMod φ p hV) :=
  inferInstanceAs (AddCommGroup (Additive B))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.instAddCommGroupEOneMod

theorem eOneMod_nsmul (x : EOneMod φ p hV) : p • x = 0 := by
  show (p • Additive.ofMul (Additive.toMul x) : Additive B) = Additive.ofMul 1
  rw [← ofMul_pow, hV]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eOneMod_nsmul

instance instModuleZModEOneMod : Module (ZMod p) (EOneMod φ p hV) :=
  AddCommGroup.zmodModule eOneMod_nsmul

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.instModuleZModEOneMod

/-- `φ q` as an additive endomorphism of `EOneMod`. -/
def eOneAddHom (q : Q) : EOneMod φ p hV →+ EOneMod φ p hV where
  toFun x := (Additive.ofMul (φ q (Additive.toMul x)) : Additive B)
  map_zero' := by
    show (Additive.ofMul (φ q 1) : Additive B) = Additive.ofMul 1
    rw [map_one]
  map_add' x y := by
    show (Additive.ofMul (φ q (Additive.toMul x * Additive.toMul y)) : Additive B) =
      Additive.ofMul (φ q (Additive.toMul x) * φ q (Additive.toMul y))
    rw [map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eOneAddHom

/-- The `F_p`-linear representation of `Q` on `EOneMod` induced by `φ`. -/
def eOneRep : Representation (ZMod p) Q (EOneMod φ p hV) where
  toFun q := (eOneAddHom (φ := φ) (p := p) (hV := hV) q).toZModLinearMap p
  map_one' := LinearMap.ext fun x => by
    show (Additive.ofMul (φ 1 (Additive.toMul x)) : Additive B) = x
    rw [map_one, MulAut.one_apply, ofMul_toMul]
  map_mul' q r := LinearMap.ext fun x => by
    show (Additive.ofMul (φ (q * r) (Additive.toMul x)) : Additive B) =
      Additive.ofMul (φ q (Additive.toMul (Additive.ofMul (φ r (Additive.toMul x)))))
    rw [map_mul, MulAut.mul_apply, toMul_ofMul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eOneRep

noncomputable instance instModuleEOneMod :
    Module (MonoidAlgebra (ZMod p) Q) (EOneMod φ p hV) :=
  Module.compHom (EOneMod φ p hV) (eOneRep (φ := φ) (p := p) (hV := hV)).asAlgebraHom.toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.instModuleEOneMod

theorem eOne_smul (q : Q) (x : EOneMod φ p hV) :
    MonoidAlgebra.of (ZMod p) Q q • x =
      (Additive.ofMul (φ q (Additive.toMul x)) : Additive B) := by
  show (eOneRep (φ := φ) (p := p) (hV := hV)).asAlgebraHom (MonoidAlgebra.of (ZMod p) Q q) x = _
  rw [Representation.asAlgebraHom_of]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eOne_smul

theorem eOne_mem_span_smul (N : Submodule (MonoidAlgebra (ZMod p) Q) (EOneMod φ p hV))
    (q : Q) (b : B) (hb : (Additive.ofMul b : EOneMod φ p hV) ∈ N) :
    (Additive.ofMul (φ q b) : EOneMod φ p hV) ∈ N := by
  have h := N.smul_mem (MonoidAlgebra.of (ZMod p) Q q) hb
  rw [eOne_smul] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eOne_mem_span_smul

theorem eOne_finite (hfg : Group.FG (B ⋊[φ] Q)) :
    Module.Finite (MonoidAlgebra (ZMod p) Q) (EOneMod φ p hV) := by
  obtain ⟨T, hT⟩ := hfg.out
  let S : Set (EOneMod φ p hV) :=
    (fun x : B ⋊[φ] Q => (Additive.ofMul x.left : EOneMod φ p hV)) '' (T : Set (B ⋊[φ] Q))
  let N : Submodule (MonoidAlgebra (ZMod p) Q) (EOneMod φ p hV) := Submodule.span _ S
  let G0 : Subgroup (B ⋊[φ] Q) :=
    { carrier := {x | (Additive.ofMul x.left : EOneMod φ p hV) ∈ N}
      one_mem' := show (Additive.ofMul (1 : B) : EOneMod φ p hV) ∈ N from N.zero_mem
      mul_mem' := by
        intro a b ha hb
        have ha' : (Additive.ofMul a.left : EOneMod φ p hV) ∈ N := ha
        have hb' : (Additive.ofMul (φ a.right b.left) : EOneMod φ p hV) ∈ N :=
          eOne_mem_span_smul N a.right b.left hb
        exact N.add_mem ha' hb'
      inv_mem' := by
        intro a ha
        have ha' : (Additive.ofMul a.left⁻¹ : EOneMod φ p hV) ∈ N := N.neg_mem ha
        exact eOne_mem_span_smul N a.right⁻¹ a.left⁻¹ ha' }
  have hle : Subgroup.closure (T : Set (B ⋊[φ] Q)) ≤ G0 := by
    rw [Subgroup.closure_le]
    intro x hx
    show (Additive.ofMul x.left : EOneMod φ p hV) ∈ N
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have htop : ∀ b : B, (Additive.ofMul b : EOneMod φ p hV) ∈ N := by
    intro b
    have hmem : (SemidirectProduct.inl b : B ⋊[φ] Q) ∈ Subgroup.closure (T : Set (B ⋊[φ] Q)) := by
      rw [hT]
      exact Subgroup.mem_top _
    exact hle hmem
  refine ⟨Submodule.fg_def.mpr ⟨S, T.finite_toSet.image _, ?_⟩⟩
  exact eq_top_iff.mpr fun x _ => htop (Additive.toMul x)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eOne_finite

end EOneModule

end GroupApproximation.BooneHigman.Metabelian.Coprimary
