import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Finiteness.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Descending an exponent-`p` module from `(ℤ/p^e)[Q]` to `F_p[Q]` (bh-met-79)

Let `M` be a `(ℤ/p^e)[Q]`-module that also carries a `ZMod p`-module structure; in practice
this comes from `p • M = 0` through `AddCommGroup.zmodModule`.  Each `a ∈ (ℤ/p^e)[Q]` acts
`ZMod p`-linearly, which gives a monoid hom `Q →* End_{F_p}(M)`.  Lifting it gives an
`F_p`-algebra hom `F_p[Q] →ₐ End_{F_p}(M)`, and so an `F_p[Q]`-module structure on `M` in
which `q` acts exactly as before.  Finiteness transfers: a finite `(ℤ/p^e)[Q]`-generating set
also generates `M` over `F_p[Q]`, because the `F_p[Q]`-span of `S` is closed under
`(ℤ/p^e)[Q]`.  The proof uses `MonoidAlgebra.induction_on`: scalars `c ∈ ℤ/p^e` act as
`c.val`-fold sums.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

section EndRep

variable {p e : ℕ} {Q M : Type*} [CommGroup Q] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M] [Module (ZMod p) M]

variable (p) in
/-- Multiplication by `a ∈ (ℤ/p^e)[Q]` as a `ZMod p`-linear endomorphism of `M`. -/
def eHighCoprimaryEnd (a : MonoidAlgebra (ZMod (p ^ e)) Q) : Module.End (ZMod p) M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := ZMod.map_smul (DistribSMul.toAddMonoidHom M a) c m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryEnd

theorem eHighCoprimaryEnd_apply (a : MonoidAlgebra (ZMod (p ^ e)) Q) (m : M) :
    eHighCoprimaryEnd p (M := M) a m = a • m :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryEnd_apply

variable (p e Q M) in
/-- The action of `Q` on `M` as a monoid hom into `End_{F_p}(M)`. -/
noncomputable def eHighCoprimaryRep : Q →* Module.End (ZMod p) M where
  toFun q := eHighCoprimaryEnd p (MonoidAlgebra.of (ZMod (p ^ e)) Q q)
  map_one' := by
    refine LinearMap.ext fun m => ?_
    show MonoidAlgebra.of (ZMod (p ^ e)) Q 1 • m = m
    rw [map_one, one_smul]
  map_mul' q r := by
    refine LinearMap.ext fun m => ?_
    show MonoidAlgebra.of (ZMod (p ^ e)) Q (q * r) • m =
      MonoidAlgebra.of (ZMod (p ^ e)) Q q • MonoidAlgebra.of (ZMod (p ^ e)) Q r • m
    rw [map_mul, mul_smul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryRep

variable (p e Q M) in
/-- The lifted `F_p`-algebra hom `F_p[Q] →ₐ End_{F_p}(M)`. -/
noncomputable def eHighCoprimaryAlgHom :
    MonoidAlgebra (ZMod p) Q →ₐ[ZMod p] Module.End (ZMod p) M :=
  MonoidAlgebra.lift (ZMod p) (Module.End (ZMod p) M) Q (eHighCoprimaryRep p e Q M)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryAlgHom

theorem eHighCoprimaryAlgHom_of (q : Q) (m : M) :
    eHighCoprimaryAlgHom p e Q M (MonoidAlgebra.of (ZMod p) Q q) m =
      MonoidAlgebra.of (ZMod (p ^ e)) Q q • m :=
  LinearMap.congr_fun (MonoidAlgebra.lift_of (R := ZMod p) (eHighCoprimaryRep p e Q M) q) m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryAlgHom_of

variable (p e Q M) in
/-- The descended `F_p[Q]`-module structure on `M`, as a non-instance. -/
noncomputable abbrev eHighCoprimaryFpModule : Module (MonoidAlgebra (ZMod p) Q) M :=
  Module.compHom M (eHighCoprimaryAlgHom p e Q M).toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryFpModule

end EndRep

section Finite

variable {p e : ℕ} {Q M : Type*} [CommGroup Q] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M] [Module (MonoidAlgebra (ZMod p) Q) M]

/-- If each `q ∈ Q` acts the same way through `F_p[Q]` and through `(ℤ/p^e)[Q]`, then
finiteness over `(ℤ/p^e)[Q]` implies finiteness over `F_p[Q]`. -/
theorem eHighCoprimaryFp_finite [NeZero (p ^ e)]
    (hof : ∀ (q : Q) (m : M),
      MonoidAlgebra.of (ZMod p) Q q • m = MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)
    (hfin : Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M) :
    Module.Finite (MonoidAlgebra (ZMod p) Q) M := by
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp hfin.fg_top
  refine Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨S, hSfin, ?_⟩)
  have hclos : ∀ (r : MonoidAlgebra (ZMod (p ^ e)) Q) {x : M},
      x ∈ Submodule.span (MonoidAlgebra (ZMod p) Q) S →
        r • x ∈ Submodule.span (MonoidAlgebra (ZMod p) Q) S := by
    intro r x hx
    refine MonoidAlgebra.induction_on
      (p := fun r : MonoidAlgebra (ZMod (p ^ e)) Q =>
        r • x ∈ Submodule.span (MonoidAlgebra (ZMod p) Q) S) r ?_ ?_ ?_
    · intro q
      show MonoidAlgebra.of (ZMod (p ^ e)) Q q • x ∈
        Submodule.span (MonoidAlgebra (ZMod p) Q) S
      rw [← hof q x]
      exact Submodule.smul_mem _ _ hx
    · intro a b ha hb
      show (a + b) • x ∈ Submodule.span (MonoidAlgebra (ZMod p) Q) S
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
    · intro c a ha
      show (c • a) • x ∈ Submodule.span (MonoidAlgebra (ZMod p) Q) S
      rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul (ZMod (p ^ e)), smul_assoc]
      exact nsmul_mem ha c.val
  let N' : Submodule (MonoidAlgebra (ZMod (p ^ e)) Q) M :=
    { carrier := (Submodule.span (MonoidAlgebra (ZMod p) Q) S : Set M)
      add_mem' := fun ha hb =>
        Submodule.add_mem (Submodule.span (MonoidAlgebra (ZMod p) Q) S) ha hb
      zero_mem' := Submodule.zero_mem (Submodule.span (MonoidAlgebra (ZMod p) Q) S)
      smul_mem' := fun r _ hx => hclos r hx }
  have hle : Submodule.span (MonoidAlgebra (ZMod (p ^ e)) Q) S ≤ N' := by
    rw [Submodule.span_le]
    show S ⊆ (Submodule.span (MonoidAlgebra (ZMod p) Q) S : Set M)
    exact Submodule.subset_span
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  have hmem : x ∈ Submodule.span (MonoidAlgebra (ZMod (p ^ e)) Q) S := by
    rw [hS]
    exact Submodule.mem_top
  exact hle hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighCoprimaryFp_finite

end Finite

end GroupApproximation.BooneHigman.Metabelian.Coprimary
