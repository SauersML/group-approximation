import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteType
import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.BooneHigman.Metabelian.AffineFPRelations

/-!
# The finitely presented group `PresAff` (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp-proof`
(`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2).  For a finite set `S ⊆ R` we take
the free product `E_I(R) ∗ F(I)` modulo the finitely many relations

* (C1) `⁅x_{ij}(ε), τ_k⁆` for `ε ∈ S`, `k ≠ j`;
* (C2) `x_{ij}(1) τ_j x_{ij}(1)⁻¹ (τ_j τ_i)⁻¹`;
* (C3) `⁅τ_k, τ_l⁆`.
* `isFinitelyPresented_presAff`: the quotient is finitely presented when `E_I(R)` is;
* `affineRel_presAff`: its generators satisfy `AffineRel S xP τP` when `1 ∈ S` generates `R`;
* `exists_finite_ring_generators`: a finitely generated ring has such an `S`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped commutatorElement

section Defs

variable (I R : Type*) [Fintype I] [DecidableEq I] [CommRing R]

/-- The free product `E_I(R) ∗ F(I)`. -/
abbrev FreeAff : Type _ := Monoid.Coprod (elementaryGroup I R) (FreeGroup I)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.FreeAff

/-- The relators (C1). -/
def relsC1 (S : Set R) : Set (FreeAff I R) :=
  {w | ∃ (i j : I) (h : i ≠ j) (ε : R), ε ∈ S ∧ ∃ k : I, k ≠ j ∧
    w = ⁅(Monoid.Coprod.inl (elementaryRoot i j h ε) : FreeAff I R),
      Monoid.Coprod.inr (FreeGroup.of k)⁆}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.relsC1

/-- The relators (C2). -/
def relsC2 : Set (FreeAff I R) :=
  {w | ∃ (i j : I) (h : i ≠ j),
    w = (Monoid.Coprod.inl (elementaryRoot i j h (1 : R)) : FreeAff I R) *
      Monoid.Coprod.inr (FreeGroup.of j) * (Monoid.Coprod.inl (elementaryRoot i j h (1 : R)))⁻¹ *
      (Monoid.Coprod.inr (FreeGroup.of j) * Monoid.Coprod.inr (FreeGroup.of i))⁻¹}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.relsC2

/-- The relators (C3). -/
def relsC3 : Set (FreeAff I R) :=
  {w | ∃ k l : I,
    w = ⁅(Monoid.Coprod.inr (FreeGroup.of k) : FreeAff I R), Monoid.Coprod.inr (FreeGroup.of l)⁆}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.relsC3

/-- All relators. -/
abbrev rels (S : Set R) : Set (FreeAff I R) := relsC1 I R S ∪ relsC2 I R ∪ relsC3 I R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.rels

/-- The normal subgroup of relations. -/
abbrev relN (S : Set R) : Subgroup (FreeAff I R) := Subgroup.normalClosure (rels I R S)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.relN

/-- The presented group. -/
abbrev PresAff (S : Set R) : Type _ := FreeAff I R ⧸ relN I R S

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.PresAff

/-- The image of `E_I(R)` in the presented group. -/
def φP (S : Set R) : elementaryGroup I R →* PresAff I R S :=
  (QuotientGroup.mk' (relN I R S)).comp Monoid.Coprod.inl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.φP

/-- The Steinberg generators of the presented group. -/
def xP (S : Set R) (i j : I) (h : i ≠ j) (r : R) : PresAff I R S :=
  φP I R S (elementaryRoot i j h r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.xP

/-- The translation generators of the presented group. -/
def τP (S : Set R) (k : I) : PresAff I R S :=
  QuotientGroup.mk' (relN I R S) (Monoid.Coprod.inr (FreeGroup.of k))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.τP

end Defs

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem rels_finite {S : Set R} (hS : S.Finite) : (rels I R S).Finite := by
  haveI := hS.to_subtype
  have h1 : (relsC1 I R S).Finite := by
    refine (Set.finite_range fun p : I × I × S × I =>
      if hp : p.1 = p.2.1 ∨ p.2.2.2 = p.2.1 then (1 : FreeAff I R) else
        ⁅(Monoid.Coprod.inl (elementaryRoot p.1 p.2.1 (not_or.mp hp).1 (p.2.2.1 : R)) :
          FreeAff I R), Monoid.Coprod.inr (FreeGroup.of p.2.2.2)⁆).subset ?_
    rintro _ ⟨i, j, h, ε, hε, k, hk, rfl⟩
    exact ⟨(i, j, ⟨ε, hε⟩, k), dif_neg (not_or.mpr ⟨h, hk⟩)⟩
  have h2 : (relsC2 I R).Finite := by
    refine (Set.finite_range fun p : I × I =>
      if hp : p.1 = p.2 then (1 : FreeAff I R) else
        (Monoid.Coprod.inl (elementaryRoot p.1 p.2 hp (1 : R)) : FreeAff I R) *
          Monoid.Coprod.inr (FreeGroup.of p.2) *
          (Monoid.Coprod.inl (elementaryRoot p.1 p.2 hp (1 : R)))⁻¹ *
          (Monoid.Coprod.inr (FreeGroup.of p.2) *
            Monoid.Coprod.inr (FreeGroup.of p.1))⁻¹).subset ?_
    rintro _ ⟨i, j, h, rfl⟩
    exact ⟨(i, j), dif_neg h⟩
  have h3 : (relsC3 I R).Finite := by
    refine (Set.finite_range fun p : I × I =>
      ⁅(Monoid.Coprod.inr (FreeGroup.of p.1) : FreeAff I R),
        Monoid.Coprod.inr (FreeGroup.of p.2)⁆).subset ?_
    rintro _ ⟨k, l, rfl⟩
    exact ⟨(k, l), rfl⟩
  exact (h1.union h2).union h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.rels_finite

/-- The presented group is finitely presented once `E_I(R)` is. -/
theorem isFinitelyPresented_presAff [Group.IsFinitelyPresented (elementaryGroup I R)]
    {S : Set R} (hS : S.Finite) : Group.IsFinitelyPresented (PresAff I R S) :=
  Group.IsFinitelyPresented.quotient (relN I R S) ⟨rels I R S, rels_finite hS, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.isFinitelyPresented_presAff

/-- A finitely generated commutative ring has a finite generating set containing `1`. -/
theorem exists_finite_ring_generators (A : Type*) [CommRing A]
    [Algebra.FiniteType ℤ A] : ∃ t : Set A, t.Finite ∧ (1 : A) ∈ t ∧ Subring.closure t = ⊤ := by
  obtain ⟨t, ht, hadj⟩ := Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := ℤ) (A := A))
  refine ⟨insert 1 t, ht.insert 1, Set.mem_insert 1 t, ?_⟩
  apply top_unique
  intro r _
  have hr : r ∈ Algebra.adjoin ℤ t := hadj ▸ Algebra.mem_top
  rw [Algebra.adjoin_int] at hr
  exact Subring.closure_mono (Set.subset_insert 1 t) (mem_subalgebraOfSubring.mp hr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.exists_finite_ring_generators

/-- The generators of the presented group satisfy the affine relations. -/
theorem affineRel_presAff {S : Set R} (h1 : (1 : R) ∈ S) (hcl : Subring.closure S = ⊤)
    (hI : 4 ≤ Fintype.card I) : AffineRel S (xP I R S) (τP I R S) where
  add i j h a b :=
    (congrArg (φP I R S) (elementaryRoot_mul i j h a b).symm).trans (map_mul (φP I R S) _ _)
  comm i j k l hij hkl hjk hli a b :=
    (elementaryRoot_commute_of_ne i j k l hij hkl hjk hli a b).map (φP I R S)
  adj i j k hij hjk hik a b :=
    (map_commutatorElement (φP I R S) _ _).symm.trans
      (congrArg (φP I R S) (elementaryRoot_commutator i j k hij hjk hik a b))
  c1 i j h ε hε k hk := by
    have hw : ⁅(Monoid.Coprod.inl (elementaryRoot i j h ε) : FreeAff I R),
        Monoid.Coprod.inr (FreeGroup.of k)⁆ ∈ rels I R S :=
      Set.mem_union_left _ (Set.mem_union_left _ ⟨i, j, h, ε, hε, k, hk, rfl⟩)
    have e : QuotientGroup.mk' (relN I R S) ⁅(Monoid.Coprod.inl (elementaryRoot i j h ε) :
        FreeAff I R), Monoid.Coprod.inr (FreeGroup.of k)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hw)
    rw [map_commutatorElement] at e
    exact commutatorElement_eq_one_iff_commute.mp e
  c2 i j h := by
    have hw : (Monoid.Coprod.inl (elementaryRoot i j h (1 : R)) : FreeAff I R) *
        Monoid.Coprod.inr (FreeGroup.of j) *
        (Monoid.Coprod.inl (elementaryRoot i j h (1 : R)))⁻¹ *
        (Monoid.Coprod.inr (FreeGroup.of j) * Monoid.Coprod.inr (FreeGroup.of i))⁻¹ ∈
          rels I R S :=
      Set.mem_union_left _ (Set.mem_union_right _ ⟨i, j, h, rfl⟩)
    have e : QuotientGroup.mk' (relN I R S)
        ((Monoid.Coprod.inl (elementaryRoot i j h (1 : R)) : FreeAff I R) *
          Monoid.Coprod.inr (FreeGroup.of j) *
          (Monoid.Coprod.inl (elementaryRoot i j h (1 : R)))⁻¹ *
          (Monoid.Coprod.inr (FreeGroup.of j) * Monoid.Coprod.inr (FreeGroup.of i))⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hw)
    simp only [map_mul, map_inv] at e
    exact mul_inv_eq_one.mp e
  c3 k l := by
    have hw : ⁅(Monoid.Coprod.inr (FreeGroup.of k) : FreeAff I R),
        Monoid.Coprod.inr (FreeGroup.of l)⁆ ∈ rels I R S :=
      Set.mem_union_right _ ⟨k, l, rfl⟩
    have e : QuotientGroup.mk' (relN I R S) ⁅(Monoid.Coprod.inr (FreeGroup.of k) :
        FreeAff I R), Monoid.Coprod.inr (FreeGroup.of l)⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hw)
    rw [map_commutatorElement] at e
    exact commutatorElement_eq_one_iff_commute.mp e
  one_mem := h1
  closure := hcl
  four := exists_ne_three hI

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.affineRel_presAff

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
