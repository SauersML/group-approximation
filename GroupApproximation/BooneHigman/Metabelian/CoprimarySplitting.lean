import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.GroupRing.Noetherian
import GroupApproximation.BooneHigman.GroupRing.Generation
import GroupApproximation.BooneHigman.Metabelian.CoprimaryHall
import GroupApproximation.Meta.AxiomGuard

/-!
# Splitting a f.g. metabelian group into pieces of pure characteristic (lane bh-met-04)

Research node `fg-metabelian-coprimary-quotients-proof`, part (a), in full.  Let `G` be a finitely
generated metabelian group and `M = G' / G''` its derived module over `R = ℤ[Gᵃᵇ]`.

1. `R` is Noetherian (`GroupRing.isNoetherianRing_intGroupRing`) and `M` is a finite `R`-module
   (`module_finite`, Hall).
2. Lasker--Noether (`Primary.exists_coprimary_decomposition`): `0 = S_1 ∩ ... ∩ S_n` with each
   `M ⧸ S_j` coprimary, hence torsion-free or killed by a prime power
   (`IsCoprimaryWith.torsionFree_or_primeExponent`).
3. The pieces `N_j = pieceSubgroup S_j` are normal, and `G ⧸ N_j` has pure characteristic
   (`isPureCharacteristic_zero`, `isPureCharacteristic_prime`).
4. Since `G'' = 1`, the `N_j` meet trivially (`eq_one_of_forall_mem_piece`).

The decomposition may have `n = 0` pieces, which happens exactly when `G` is abelian, and then no
family of quotients would be indexed.  So the piece `pieceSubgroup ⊤ = G'` is prepended
(`consTop`): `G ⧸ G'` is abelian, of characteristic `0` in the sense of `IsPureCharacteristic`.

Main declaration: `exists_pureCharacteristic_splitting`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

variable {G : Type*} [Group G]

/-- The coprimary components with `⊤` prepended, so that there is at least one piece. -/
def consTop {n : ℕ}
    (S : Fin n → Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) :
    Fin (n + 1) → Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G) :=
  Fin.cons ⊤ S

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.consTop

theorem consTop_zero {n : ℕ}
    (S : Fin n → Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) :
    consTop S 0 = ⊤ :=
  Fin.cons_zero _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.consTop_zero

theorem consTop_succ {n : ℕ}
    (S : Fin n → Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)) (j : Fin n) :
    consTop S j.succ = S j :=
  Fin.cons_succ _ _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.consTop_succ

/-- The piece of `⊤` is `G'`, and `G ⧸ G'` has characteristic `0`. -/
theorem isPureCharacteristic_top :
    IsPureCharacteristic
      (G ⧸ pieceSubgroup (⊤ : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)))
      0 :=
  isPureCharacteristic_zero _ fun _ _ _ _ => Submodule.mem_top

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isPureCharacteristic_top

/-- The piece of a coprimary component has pure characteristic. -/
theorem exists_isPureCharacteristic_of_coprimary
    (T : Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G))
    {P : Ideal (MonoidAlgebra ℤ (Abelianization G))} {e : ℕ}
    (hT : Primary.IsCoprimaryWith (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G ⧸ T) P e) :
    ∃ c : ℕ, IsPureCharacteristic (G ⧸ pieceSubgroup T) c := by
  rcases hT.torsionFree_or_primeExponent with h | ⟨p, hp, -, hq⟩
  · refine ⟨0, isPureCharacteristic_zero T fun k hk y hy => ?_⟩
    have h1 : k • T.mkQ y = k • (0 : DerivedModule G ⧸ T) :=
      (map_zsmul T.mkQ k y).symm.trans
        (((Submodule.Quotient.mk_eq_zero T).mpr hy).trans (zsmul_zero k).symm)
    exact (Submodule.Quotient.mk_eq_zero T).mp (h k hk h1)
  · exact ⟨p, isPureCharacteristic_prime T hp fun y =>
      (Submodule.Quotient.mk_eq_zero T).mp ((map_zsmul T.mkQ _ y).trans (hq _))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_isPureCharacteristic_of_coprimary

/-- Every piece of `consTop S` has pure characteristic. -/
theorem exists_isPureCharacteristic_consTop {n : ℕ}
    (S : Fin n → Submodule (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G))
    {P : Fin n → Ideal (MonoidAlgebra ℤ (Abelianization G))} {e : Fin n → ℕ}
    (hP : ∀ j, Primary.IsCoprimaryWith (MonoidAlgebra ℤ (Abelianization G))
      (DerivedModule G ⧸ S j) (P j) (e j)) (i : Fin (n + 1)) :
    ∃ c : ℕ, IsPureCharacteristic (G ⧸ pieceSubgroup (consTop S i)) c := by
  induction i using Fin.cases with
  | zero =>
    rw [consTop_zero]
    exact ⟨0, isPureCharacteristic_top⟩
  | succ j =>
    rw [consTop_succ]
    exact exists_isPureCharacteristic_of_coprimary (S j) (hP j)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_isPureCharacteristic_consTop

variable (G) in
/-- **Coprimary splitting, group-theoretic part.** A finitely generated metabelian group has
finitely many normal subgroups `N_i ≤ G'`, meeting trivially, with every `G ⧸ N_i` of pure
characteristic. -/
theorem exists_pureCharacteristic_splitting [Group.FG G] (hG : IsMetabelianGroup G) :
    ∃ (n : ℕ) (N : Fin n → Subgroup G) (_ : ∀ i, (N i).Normal),
      (∀ g : G, (∀ i, g ∈ N i) → g = 1) ∧
        ∀ i, N i ≤ commutator G ∧ ∃ c : ℕ, IsPureCharacteristic (G ⧸ N i) c := by
  haveI := GroupRing.group_fg_abelianization G
  haveI := GroupRing.isNoetherianRing_intGroupRing (Abelianization G)
  haveI := module_finite G
  obtain ⟨n, S, P, e, hS, -, hP⟩ :=
    Primary.exists_coprimary_decomposition (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)
  refine ⟨n + 1, fun i => pieceSubgroup (consTop S i), fun i => pieceSubgroup_normal _,
    fun g hg => ?_, fun i => ⟨pieceSubgroup_le _, exists_isPureCharacteristic_consTop S hP i⟩⟩
  have hA : g ∈ commutator G := pieceSubgroup_le (consTop S 0) (hg 0)
  refine eq_one_of_forall_mem_piece hG S hS hA fun j => ?_
  have h : g ∈ pieceSubgroup (consTop S j.succ) := hg j.succ
  rw [consTop_succ] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_pureCharacteristic_splitting

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
