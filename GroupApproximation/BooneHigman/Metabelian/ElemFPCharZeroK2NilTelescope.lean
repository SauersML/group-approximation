import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# Vanishing of the nil part of `K₂(N, A[t_0..t_{k-1}])` from the generic gap pair

Lane `bh-met-37`, generic module.  Over an arbitrary commutative base ring `A`:

* `eq_one_of_K2IndexMap_eq_one_of_nilStab`: **telescoping on an augmentation kernel.**  Let
  `cc : R → Z` be a ring map.  Suppose that for every rank `m ≥ n`, an element of `K₂(m, R)`
  killed by `cc` and by `K2Stab` is trivial.  Then an element `u ∈ K₂(n, R)` killed by `cc` that
  dies after padding is trivial.  The padded elements stay in the kernel of `cc`, because
  coefficient maps commute with padding (`K2IndexMap_K2Map`).  This replaces the char-`p` use of
  `Full.LVH2GL3.eq_one_of_indexMap_eq_one`, which needs injectivity on all of `K₂(m, R)`.  That is
  not available over `ℤ[1/m]`, whose `K₂` is not zero.
* `polyK2NilPosOver_of_oneVar_of_diag`, `polyK2NilPosOver_of_gap`: for `d ≥ 4`, the gap pair
  `PolyK2NilGapStatementOver A d` gives `PolyK2NilPosStatementOver A d`.  Take `u ∈ K₂(N, A[σ])`,
  `N ≥ k + d`, with `ev₀ u = 1`.  The nil part gives some rank `M` where `u` dies.  Stability on
  `ker ev₀` at every rank `m ≥ N ≥ k + d` telescopes back to `u = 1`.
* `polyK2StabRangeDiagOver_of_nilPos`, `polyK2OneVarNilOver_of_nilPos`,
  `polyK2NilGapOver_of_nilPos`: the converses at `d = 4`.  So at `d = 4` the pair is not
  logically stronger than the vanishing statement.  What the pair removes is the proof content:
  the induction on the number of variables, the passage to all ranks and the telescoping.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section Telescope

variable {R Z : Type*} [Ring R] [Ring Z]

/-- Padding along `Fin n ↪ Fin n` is the identity on `K₂`. -/
theorem K2IndexMap_castLEEmb_self {n : ℕ} (h : n ≤ n) (u : K2n n R) :
    K2IndexMap (Fin.castLEEmb h) u = u :=
  Subtype.ext (GroupApproximation.Full.LVH2GL3.indexMap_castLEEmb_self h (u : St n R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2IndexMap_castLEEmb_self

/-- `K2Stab n R` is padding along `Fin.castLEEmb (n ≤ n + 1)`. -/
theorem K2Stab_eq_K2IndexMap_castLEEmb {n : ℕ} (u : K2n n R) :
    K2Stab n R u = K2IndexMap (Fin.castLEEmb (Nat.le_succ n)) u :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Stab_eq_K2IndexMap_castLEEmb

/-- **Telescoping on the kernel of an augmentation.**  If `K2Stab m R` is injective on the kernel
of `cc` for every `m ≥ n`, then an element of `K₂(n, R)` in the kernel of `cc` that dies in some
`K₂(M, R)` is trivial. -/
theorem eq_one_of_K2IndexMap_eq_one_of_nilStab (cc : R →+* Z) {n : ℕ}
    (hT : ∀ m : ℕ, n ≤ m → ∀ v : K2n m R, K2Map cc v = 1 → K2Stab m R v = 1 → v = 1)
    {u : K2n n R} (hu0 : K2Map cc u = 1) (M : ℕ) (h : n ≤ M)
    (hM : K2IndexMap (Fin.castLEEmb h) u = 1) : u = 1 := by
  revert hM
  induction M, h using Nat.le_induction with
  | base =>
    intro hM
    exact (K2IndexMap_castLEEmb_self (Nat.le_refl n) u).symm.trans hM
  | succ M hnM ih =>
    intro hM
    apply ih
    apply hT M hnM (K2IndexMap (Fin.castLEEmb hnM) u)
    · rw [← K2IndexMap_K2Map, hu0, map_one]
    · rw [K2Stab_eq_K2IndexMap_castLEEmb, K2IndexMap_castLEEmb_castLEEmb]
      exact hM

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.eq_one_of_K2IndexMap_eq_one_of_nilStab

end Telescope

/-- **Generic endpoint.**  For `d ≥ 4`, the one-variable nil part and diagonal stability on
`ker ev₀` at offset `d` give vanishing of `ker ev₀` on `K₂(N, A[s_1..s_k])` for `N ≥ k + d`. -/
theorem polyK2NilPosOver_of_oneVar_of_diag (A : Type*) [CommRing A] {d : ℕ} (hd : 4 ≤ d)
    (hone : PolyK2OneVarNilStatementOver A) (hdiag : PolyK2StabRangeDiagStatementOver A d) :
    PolyK2NilPosStatementOver A d := by
  intro k N hk hkN u hu
  obtain ⟨M, hNM, hM⟩ := polyK2NilOver_of_oneVar A hone k N (by omega) (by omega) u hu
  exact eq_one_of_K2IndexMap_eq_one_of_nilStab
    (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A)
    (fun m hm v hv0 hv ↦
      polyK2NilStabilityOver_of_diag A d hdiag k m hk (hkN.trans hm) v hv0 hv)
    hu M hNM hM

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilPosOver_of_oneVar_of_diag

/-- The generic endpoint, stated with the gap pair. -/
theorem polyK2NilPosOver_of_gap (A : Type*) [CommRing A] {d : ℕ} (hd : 4 ≤ d)
    (h : PolyK2NilGapStatementOver A d) : PolyK2NilPosStatementOver A d :=
  polyK2NilPosOver_of_oneVar_of_diag A hd h.1 h.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilPosOver_of_gap

/-- Converse, stability half: vanishing of `ker ev₀` at offset `d` gives diagonal stability on
`ker ev₀` at offset `d`. -/
theorem polyK2StabRangeDiagOver_of_nilPos (A : Type*) [CommRing A] (d : ℕ)
    (h : PolyK2NilPosStatementOver A d) : PolyK2StabRangeDiagStatementOver A d :=
  fun k hk u hu0 _ ↦ h k (k + d) hk le_rfl u hu0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2StabRangeDiagOver_of_nilPos

/-- Converse, nil half: vanishing of `ker ev₀` at an offset `d ≤ 4` gives the one-variable nil
part (with `M = N`), through `A[s_0..s_k] ≅ A[s_1..s_k][s_0]`. -/
theorem polyK2OneVarNilOver_of_nilPos (A : Type*) [CommRing A] {d : ℕ} (hd : d ≤ 4)
    (h : PolyK2NilPosStatementOver A d) : PolyK2OneVarNilStatementOver A := by
  intro k N hkN u hu
  have hv := h (k + 1) N (Nat.succ_pos k) (by omega)
    (K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.symm.toRingHom u)
    (by
      rw [← constantCoeff_comp_finSuccEquiv (R := A) k, ← K2Map_K2Map, ← K2Map_K2Map,
        K2Map_K2Map_of_comp_eq_id _ _
          (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom_comp_symm_toRingHom,
        hu, map_one])
  refine ⟨N, le_rfl, ?_⟩
  rw [K2IndexMap_castLEEmb_self, ← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom_comp_symm_toRingHom u, hv, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNilOver_of_nilPos

/-- At `d = 4` the gap pair is equivalent to vanishing of `ker ev₀`: this is the converse. -/
theorem polyK2NilGapOver_of_nilPos (A : Type*) [CommRing A]
    (h : PolyK2NilPosStatementOver A 4) : PolyK2NilGapStatementOver A 4 :=
  ⟨polyK2OneVarNilOver_of_nilPos A le_rfl h, polyK2StabRangeDiagOver_of_nilPos A 4 h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilGapOver_of_nilPos

end GroupApproximation.BooneHigman.Metabelian.ElemFP
