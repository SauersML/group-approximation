import GroupApproximation.Manuscript.ChainCore.BilateralThreeCellDischarge
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:bilateral-three`, first paragraph of the proof: the cell and its levels

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three`, tex 1550–1553:

> (1550–1552) Take a clopen $P$ with $T(P)\subseteq P$ and nonempty
> $D=P\setminus T(P)$.  Put $p=1_P$, $d=1_D$, and
> $f_{ab}=u^a d u^{-b}$ for $a,b\in\mathbb Z$.
> (1552–1553) Wandering gives $f_{ab}f_{ce}=\delta_{bc}f_{ae}$.
> (1553) Negative levels lie outside $P$.

Here `R_X = LC(X,k) ⋊_T ℤ` is `GroupApproximation.ClopenCrossedProduct T k`, `u` is
`ClopenCrossedProduct.unit T k`, and `1_U` is `coeff (LocallyConstant.charFn k hU)`.

## Proof route

* The data `p = 1_P`, `u` form the abstract cell `ClopenCrossedProduct.bilateralCell T k hP hTP`
  (`p` idempotent, `u p u⁻¹ ≤ p` because `T(P) ⊆ P`); its defect `p - u p u⁻¹` is `1_D`
  (`bilateralCell_d`), nonzero because `D` is nonempty (`defectD_ne_zero`), and `f_{ab}` is the
  cell's `Cell.f a b = u^a d u^{-b}` by definition.
* Wandering: the levels `u^j d u^{-j}` are pairwise orthogonal, which is `Cell.f_mul_f`.
* Negative levels: for `n ≥ 0` and `y ∈ D`, `T^{-(n+1)} y ∉ P`, since otherwise
  `y = T^{n+1}(T^{-(n+1)} y) ∈ T(P)` (the forward orbit of `P` stays in `P`). Algebraically,
  `p f_{ab} = 0` for `a < 0` and `f_{ab} p = 0` for `b < 0` (`Cell.p_mul_f`, `Cell.f_mul_p`).

No hypothesis beyond the printed ones (`P` clopen, `T(P) ⊆ P`, `D ≠ ∅`) is used; the
standing compactness/metrizability assumptions of the section are not needed.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace BilateralA

section Levels

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Field k] {P : Set X}

/-- **"Take a clopen $P$ with $T(P)\subseteq P$ and nonempty $D=P\setminus T(P)$.  Put $p=1_P$,
$d=1_D$, and $f_{ab}=u^a d u^{-b}$ for $a,b\in\mathbb Z$."** (tex 1550–1552).

For such `P`, the bilateral cell of `R_X` has unit `u`, idempotent `p = 1_P`, defect
`d = 1_D ≠ 0`, and matrix units `f_{ab} = u^a d u^{-b}`. -/
theorem manuscriptSentence_takeCompressedClopen (hP : IsClopen P) (hTP : T '' P ⊆ P)
    (hD : (P \ T '' P).Nonempty) :
    (ClopenCrossedProduct.bilateralCell T k hP hTP).u = ClopenCrossedProduct.unit T k ∧
      (ClopenCrossedProduct.bilateralCell T k hP hTP).p =
        ClopenCrossedProduct.coeff T k (LocallyConstant.charFn k hP) ∧
      (ClopenCrossedProduct.bilateralCell T k hP hTP).d =
        ClopenCrossedProduct.coeff T k
          (LocallyConstant.charFn k (hP.diff (ClopenCrossedProduct.isClopen_image T hP))) ∧
      (ClopenCrossedProduct.bilateralCell T k hP hTP).d ≠ 0 ∧
      ∀ a b : ℤ, (ClopenCrossedProduct.bilateralCell T k hP hTP).f a b =
        ((ClopenCrossedProduct.unit T k ^ a : (ClopenCrossedProduct T k)ˣ) :
            ClopenCrossedProduct T k) *
          (ClopenCrossedProduct.bilateralCell T k hP hTP).d *
          ((ClopenCrossedProduct.unit T k ^ (-b) : (ClopenCrossedProduct T k)ˣ) :
            ClopenCrossedProduct T k) := by
  obtain ⟨x, hx⟩ := hD
  refine ⟨rfl, rfl, ClopenCrossedProduct.bilateralCell_d T k hP hTP, ?_, fun _ _ => rfl⟩
  rw [ClopenCrossedProduct.bilateralCell_d T k hP hTP]
  exact ClopenCrossedProduct.defectD_ne_zero T k hP hx

/-- **"Wandering gives $f_{ab}f_{ce}=\delta_{bc}f_{ae}$."** (tex 1552–1553). -/
theorem manuscriptSentence_wanderingMatrixUnits (hP : IsClopen P) (hTP : T '' P ⊆ P)
    (a b c e : ℤ) :
    (ClopenCrossedProduct.bilateralCell T k hP hTP).f a b *
        (ClopenCrossedProduct.bilateralCell T k hP hTP).f c e =
      if b = c then (ClopenCrossedProduct.bilateralCell T k hP hTP).f a e else 0 :=
  (ClopenCrossedProduct.bilateralCell T k hP hTP).f_mul_f a b c e

end Levels

section Orbit

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) {P : Set X}

/-- The forward orbit of a `T`-compressed set stays inside it. -/
theorem iterate_mem_of_mem (hTP : T '' P ⊆ P) (n : ℕ) : ∀ x ∈ P, (⇑T)^[n] x ∈ P := by
  induction n with
  | zero => intro x hx; exact hx
  | succ n ih => intro x hx; exact ih (T x) (hTP (Set.mem_image_of_mem T hx))

/-- The negative levels `T^{-(n+1)}(D)` of `D = P ∖ T(P)` miss `P`. -/
theorem iterate_symm_not_mem (hTP : T '' P ⊆ P) (n : ℕ) {y : X} (hy : y ∈ P \ T '' P) :
    (⇑T.symm)^[n + 1] y ∉ P := by
  intro hmem
  have hinv : Function.RightInverse (⇑T.symm) (⇑T) := T.apply_symm_apply
  have hback : (⇑T)^[n + 1] ((⇑T.symm)^[n + 1] y) = y := hinv.iterate (n + 1) y
  have himg : (⇑T)^[n + 1] ((⇑T.symm)^[n + 1] y) ∈ T '' P :=
    iterate_mem_of_mem T (P := T '' P) (Set.image_mono hTP) n (T ((⇑T.symm)^[n + 1] y))
      (Set.mem_image_of_mem T hmem)
  rw [hback] at himg
  exact hy.2 himg

end Orbit

section Negative

variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (k : Type*) [Field k] {P : Set X}

/-- **"Negative levels lie outside $P$."** (tex 1553).

Dynamically, every negative level `T^{-(n+1)}(D)` is disjoint from `P`; algebraically, the
matrix units with a negative index are killed by `p` on that side. -/
theorem manuscriptSentence_negativeLevelsOutsideP (hP : IsClopen P) (hTP : T '' P ⊆ P) :
    (∀ n : ℕ, Disjoint ((⇑T.symm)^[n + 1] '' (P \ T '' P)) P) ∧
      (∀ a b : ℤ, a < 0 →
        (ClopenCrossedProduct.bilateralCell T k hP hTP).p *
          (ClopenCrossedProduct.bilateralCell T k hP hTP).f a b = 0) ∧
      (∀ a b : ℤ, b < 0 →
        (ClopenCrossedProduct.bilateralCell T k hP hTP).f a b *
          (ClopenCrossedProduct.bilateralCell T k hP hTP).p = 0) :=
  ⟨fun n => Set.disjoint_left.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact iterate_symm_not_mem T hTP n hy),
    fun _ b ha => (ClopenCrossedProduct.bilateralCell T k hP hTP).p_mul_f ha b,
    fun a _ hb => (ClopenCrossedProduct.bilateralCell T k hP hTP).f_mul_p a hb⟩

end Negative

end BilateralA
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralA.manuscriptSentence_takeCompressedClopen
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralA.manuscriptSentence_wanderingMatrixUnits
#audit_axioms GroupApproximation.Manuscript.NonMF.BilateralA.manuscriptSentence_negativeLevelsOutsideP
