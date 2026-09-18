import Mathlib.Data.Nat.Prime.Defs
import GroupApproximation.BooneHigman.Statement.Basic
import GroupApproximation.BooneHigman.Metabelian.CoprimaryModule
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal subgroups from submodules of the derived module (lane bh-met-04)

Research node `fg-metabelian-coprimary-quotients-proof`, steps (a)3--(a)5.  A
`ℤ[Gᵃᵇ]`-submodule `S` of the derived module `DerivedModule G = G' / G''` pulls back to the
subgroup `pieceSubgroup S = {g ∈ G' | [g] ∈ S}`, which is normal in `G` because `S` is stable under
the conjugation action.  Then:

* `(G ⧸ N)' = G' N / N` (`commutator_quotient_eq`);
* if `M ⧸ S` is torsion-free, `(G ⧸ pieceSubgroup S)'` is torsion-free
  (`isPureCharacteristic_zero`);
* if `p ^ e` kills `M ⧸ S`, `(G ⧸ pieceSubgroup S)'` has exponent dividing `p ^ e`
  (`isPureCharacteristic_prime`);
* for metabelian `G`, the pieces of a family of submodules with trivial intersection meet in
  the trivial subgroup (`eq_one_of_forall_mem_piece`).

`IsPureCharacteristic Γ c` says: `c = 0` and `Γ'` is torsion-free, or `c` is prime and `Γ'` has
exponent a power of `c`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

variable {G : Type*} [Group G]

/-- The subgroup of `G'` of elements whose class lies in the submodule `S`. -/
def pieceSubgroup (S : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) :
    Subgroup G where
  carrier := {g | ∃ h : g ∈ commutator G, dcls ⟨g, h⟩ ∈ S}
  mul_mem' := by
    rintro a b ⟨ha, hSa⟩ ⟨hb, hSb⟩
    refine ⟨(commutator G).mul_mem ha hb, ?_⟩
    show dcls ((⟨a, ha⟩ : commutator G) * ⟨b, hb⟩) ∈ S
    rw [dcls_mul]
    exact S.add_mem hSa hSb
  one_mem' := by
    refine ⟨(commutator G).one_mem, ?_⟩
    show dcls (1 : commutator G) ∈ S
    rw [dcls_one]
    exact S.zero_mem
  inv_mem' := by
    rintro x ⟨hx, hSx⟩
    refine ⟨(commutator G).inv_mem hx, ?_⟩
    show dcls (⟨x, hx⟩ : commutator G)⁻¹ ∈ S
    rw [dcls_inv]
    exact S.neg_mem hSx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pieceSubgroup

theorem mem_pieceSubgroup
    {S : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)} {g : G} :
    g ∈ pieceSubgroup S ↔ ∃ h : g ∈ commutator G, dcls ⟨g, h⟩ ∈ S :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.mem_pieceSubgroup

/-- Pieces are normal: submodules are stable under conjugation. -/
instance pieceSubgroup_normal
    (S : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) :
    (pieceSubgroup S).Normal where
  conj_mem n hn g := by
    obtain ⟨hA, hS⟩ := mem_pieceSubgroup.mp hn
    refine mem_pieceSubgroup.mpr ⟨(inferInstance : (commutator G).Normal).conj_mem n hA g, ?_⟩
    show dcls (MulAut.conjNormal g (⟨n, hA⟩ : commutator G)) ∈ S
    rw [← of_smul_dcls]
    exact S.smul_mem _ hS

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pieceSubgroup_normal

theorem pieceSubgroup_le
    (S : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) :
    pieceSubgroup S ≤ commutator G := fun _ h =>
  (mem_pieceSubgroup.mp h).elim fun hA _ => hA

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pieceSubgroup_le

/-- The derived subgroup of a quotient is the image of the derived subgroup. -/
theorem commutator_quotient_eq (N : Subgroup G) [N.Normal] :
    (commutator G).map (QuotientGroup.mk' N) = commutator (G ⧸ N) := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.commutator_quotient_eq

variable (G) in
/-- `c = 0` and `G'` is torsion-free, or `c` is prime and `G'` has exponent a power of `c`. -/
def IsPureCharacteristic (c : ℕ) : Prop :=
  (c = 0 ∧ ∀ x ∈ commutator G, ∀ n : ℕ, n ≠ 0 → x ^ n = 1 → x = 1) ∨
    (c.Prime ∧ ∃ e : ℕ, ∀ x ∈ commutator G, x ^ (c ^ e) = 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.IsPureCharacteristic

/-- A piece whose quotient module is torsion-free has characteristic zero. -/
theorem isPureCharacteristic_zero
    (S : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G))
    (hS : ∀ n : ℤ, n ≠ 0 → ∀ y : DerivedModule G, n • y ∈ S → y ∈ S) :
    IsPureCharacteristic (G ⧸ pieceSubgroup S) 0 := by
  unfold IsPureCharacteristic
  refine Or.inl ⟨rfl, fun x hx n hn hxn => ?_⟩
  rw [← commutator_quotient_eq (pieceSubgroup S)] at hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have h0 : QuotientGroup.mk' (pieceSubgroup S) (g ^ n) = 1 :=
    (map_pow (QuotientGroup.mk' (pieceSubgroup S)) g n).trans hxn
  have h1 : g ^ n ∈ pieceSubgroup S := (QuotientGroup.eq_one_iff (g ^ n)).mp h0
  obtain ⟨_, h2⟩ := mem_pieceSubgroup.mp h1
  have ez : (n : ℤ) • dcls (⟨g, hg⟩ : commutator G) = dcls ((⟨g, hg⟩ : commutator G) ^ n) :=
    (natCast_zsmul _ n).trans (dcls_pow _ n).symm
  have h3 : (n : ℤ) • dcls (⟨g, hg⟩ : commutator G) ∈ S := by
    rw [ez]
    exact h2
  have h4 : dcls (⟨g, hg⟩ : commutator G) ∈ S := hS n (Nat.cast_ne_zero.mpr hn) _ h3
  exact (QuotientGroup.eq_one_iff g).mpr (mem_pieceSubgroup.mpr ⟨hg, h4⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isPureCharacteristic_zero

/-- A piece whose quotient module is killed by `p ^ e` has characteristic `p`. -/
theorem isPureCharacteristic_prime
    (S : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) {p e : ℕ}
    (hp : p.Prime) (he : ∀ y : DerivedModule G, ((p : ℤ) ^ e) • y ∈ S) :
    IsPureCharacteristic (G ⧸ pieceSubgroup S) p := by
  unfold IsPureCharacteristic
  refine Or.inr ⟨hp, e, fun x hx => ?_⟩
  rw [← commutator_quotient_eq (pieceSubgroup S)] at hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have ez : ((p : ℤ) ^ e) • dcls (⟨g, hg⟩ : commutator G) =
      dcls ((⟨g, hg⟩ : commutator G) ^ (p ^ e)) :=
    ((congrArg (fun z : ℤ => z • dcls (⟨g, hg⟩ : commutator G)) (Nat.cast_pow p e).symm).trans
      (natCast_zsmul _ (p ^ e))).trans (dcls_pow _ (p ^ e)).symm
  have h1 : dcls ((⟨g, hg⟩ : commutator G) ^ (p ^ e)) ∈ S := by
    rw [← ez]
    exact he _
  have h2 : g ^ (p ^ e) ∈ pieceSubgroup S :=
    mem_pieceSubgroup.mpr ⟨(commutator G).pow_mem hg (p ^ e), h1⟩
  exact (map_pow (QuotientGroup.mk' (pieceSubgroup S)) g (p ^ e)).symm.trans
    ((QuotientGroup.eq_one_iff (g ^ (p ^ e))).mpr h2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isPureCharacteristic_prime

/-- In a metabelian group, the pieces of submodules with trivial intersection meet trivially. -/
theorem eq_one_of_forall_mem_piece (hG : IsMetabelianGroup G) {ι : Type*}
    (S : ι → Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G))
    (hS : ∀ m : DerivedModule G, (∀ i, m ∈ S i) → m = 0) {g : G} (hA : g ∈ commutator G)
    (hg : ∀ i, g ∈ pieceSubgroup (S i)) : g = 1 := by
  have h0 : dcls (⟨g, hA⟩ : commutator G) = 0 := hS _ fun i => by
    obtain ⟨_, h⟩ := mem_pieceSubgroup.mp (hg i)
    exact h
  have h1 : Abelianization.of (⟨g, hA⟩ : commutator G) = 1 := ofMul_eq_zero.mp h0
  have h2 : (⟨g, hA⟩ : commutator G) ∈ commutator (commutator G) := by
    rw [← Abelianization.ker_of (commutator G)]
    exact MonoidHom.mem_ker.mpr h1
  have h3 : g ∈ ⁅commutator G, commutator G⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem _ h2
  have hG' : ⁅commutator G, commutator G⁆ = ⊥ := hG
  rw [hG'] at h3
  exact Subgroup.mem_bot.mp h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eq_one_of_forall_mem_piece

/-- Quotients of metabelian groups are metabelian. -/
theorem isMetabelianGroup_quotient (hG : IsMetabelianGroup G) (N : Subgroup G) [N.Normal] :
    IsMetabelianGroup (G ⧸ N) := by
  have hG' : ⁅commutator G, commutator G⁆ = ⊥ := hG
  show ⁅commutator (G ⧸ N), commutator (G ⧸ N)⁆ = ⊥
  rw [← commutator_quotient_eq N, ← Subgroup.map_commutator, hG', Subgroup.map_bot]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isMetabelianGroup_quotient

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
