import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeGapLocal
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeLocalJacobson
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube half over `ℤ[1/m]`: reduction to maximal ideals of positive residue characteristic

Lane `bh-met-74`.  The target is the cube half of `CZCubeGapLocalStatement`,
`∀ m > 0, CZCubeGapLocalOverStatement ℤ[1/m]`.  It is **not** proved here: its content is
Quillen's `NK₂(B) = 0` for the regular ring `B = ℤ[1/m][s_1..s_k]`, locally at every maximal
ideal.  This module removes the commutative-algebra part of that local statement.

Every maximal ideal `𝔪` of `B` contains a rational prime `p` (module
`ElemFPCharZeroK2CubeLocalJacobson`: `ℤ` and `ℤ[1/m]` are Jacobson, and the
Nullstellensatz contraction `𝔪 ∩ ℤ[1/m]` is maximal).  So the local condition only has to be
checked at maximal ideals `𝔪 ∋ p`, i.e. those with residue field `B ⧸ 𝔪` of characteristic
`p > 0` (such a residue field is in fact finite, and `p ∤ m` holds automatically).

* `CZCubeLocalResidueOverStatement A`: the local cube condition, only at maximal `𝔪 ∋ p`.
* `CZCubeLocalResidueStatement`: that condition over every `ℤ[1/m]`, `m ≥ 1`.
* `czCubeLocal_gapLocalOver_of_residue`: it gives the cube half over every `ℤ[1/m]`.
* `czCubeLocal_residue_of_gapLocal`: the converse (trivial).
* `czCubeLocal_czCubeGapLocal_of_residue`: with the diagonal half it gives
  `CZCubeGapLocalStatement`.  `czCubeLocal_charZeroK2CubeGapPos_of_residue` and
  `czCubeLocal_charZeroK2CubeGapPos_of_residue_of_rowPar` go on to the root hypothesis
  `CharZeroK2CubeGapPosStatement`.

LOUD: `CZCubeLocalResidueStatement` is **logically equivalent** to the cube half; both
directions are proved below.  It is strictly smaller in proof content, because the Jacobson
property of `ℤ` and `ℤ[1/m]` and the Nullstellensatz contraction are discharged.  Truth check:
it is true, since the cube half is true (Quillen: `NK₂ = 0` for regular rings, and `B` is
regular).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Over

variable (A : Type*) [CommRing A]

/-- **The local cube condition at maximal ideals of positive residue characteristic.**  As
`CZCubeGapLocalOverStatement A`, but only for maximal ideals `𝔪` of `A[s_1..s_k]` that contain
a rational prime `p`. -/
def CZCubeLocalResidueOverStatement : Prop :=
  ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) A),
      (∀ i : Fin (k + 1), K2Map (cubeKill A i) u = 1) →
        ∀ p : ℕ, p.Prime →
          ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
            (p : MvPolynomial (Fin k) A) ∈ P →
              ∃ s : MvPolynomial (Fin k) A, s ∉ P ∧
                K2DiesAfterPadding
                  (quillenDiff (K2Map (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom u) s)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CZCubeLocalResidueOverStatement

/-- If every maximal ideal of every `A[s_1..s_k]` contains a prime, the residue-characteristic
form gives the local cube form over `A`. -/
theorem czCubeLocal_gapLocalOver_of_residueOver
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    (h : CZCubeLocalResidueOverStatement A) : CZCubeGapLocalOverStatement A := by
  intro k N hkN u hu P hP
  obtain ⟨p, hp, hpP⟩ := hres k P hP
  exact h k N hkN u hu p hp P hP hpP

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_gapLocalOver_of_residueOver

/-- Conversely, the local cube form gives the residue-characteristic form (over any `A`). -/
theorem czCubeLocal_residueOver_of_gapLocalOver (h : CZCubeGapLocalOverStatement A) :
    CZCubeLocalResidueOverStatement A :=
  fun k N hkN u hu _ _ P hP _ ↦ h k N hkN u hu P hP

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_residueOver_of_gapLocalOver

end Over

/-- **The isolated gap** (lane `bh-met-74`): over every `ℤ[1/m]` with `m ≥ 1`, the local cube
condition at the maximal ideals of `ℤ[1/m][s_1..s_k]` that contain a rational prime.  LOUD:
logically equivalent to the cube half of `CZCubeGapLocalStatement`, strictly smaller in proof
content (see the module docstring). -/
def CZCubeLocalResidueStatement : Prop :=
  ∀ m : ℕ, 0 < m → CZCubeLocalResidueOverStatement (Localization.Away (m : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CZCubeLocalResidueStatement

/-- **Endpoint (lane `bh-met-74`).**  The residue-characteristic gap gives the cube half over
every `ℤ[1/m]`. -/
theorem czCubeLocal_gapLocalOver_of_residue (h : CZCubeLocalResidueStatement) :
    ∀ m : ℕ, 0 < m → CZCubeGapLocalOverStatement (Localization.Away (m : ℤ)) :=
  fun m hm ↦ czCubeLocal_gapLocalOver_of_residueOver _
    (fun _ P hP ↦ czCubeLocal_exists_prime_mem (m : ℤ) P hP) (h m hm)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_gapLocalOver_of_residue

/-- Conversely, the cube half of `CZCubeGapLocalStatement` gives the residue gap. -/
theorem czCubeLocal_residue_of_gapLocal (h : CZCubeGapLocalStatement) :
    CZCubeLocalResidueStatement :=
  fun m hm ↦ czCubeLocal_residueOver_of_gapLocalOver _ (h m hm).1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_residue_of_gapLocal

/-- **Combined endpoint (lane `bh-met-74`).**  The residue gap and the diagonal half give
`CZCubeGapLocalStatement`. -/
theorem czCubeLocal_czCubeGapLocal_of_residue (h : CZCubeLocalResidueStatement)
    (hdiag : ∀ m : ℕ, 0 < m → PolyK2StabRangeDiagStatementOver (Localization.Away (m : ℤ)) 4) :
    CZCubeGapLocalStatement :=
  fun m hm ↦ ⟨czCubeLocal_gapLocalOver_of_residue h m hm, hdiag m hm⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_czCubeGapLocal_of_residue

/-- The residue gap and the diagonal half give the root hypothesis
`CharZeroK2CubeGapPosStatement`. -/
theorem czCubeLocal_charZeroK2CubeGapPos_of_residue (h : CZCubeLocalResidueStatement)
    (hdiag : ∀ m : ℕ, 0 < m → PolyK2StabRangeDiagStatementOver (Localization.Away (m : ℤ)) 4) :
    CharZeroK2CubeGapPosStatement :=
  charZeroK2CubeGapPos_of_czCubeGapLocal (czCubeLocal_czCubeGapLocal_of_residue h hdiag)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_charZeroK2CubeGapPos_of_residue

/-- The residue gap and row injectivity at rank `k + 4` give the root hypothesis.  (The row
input is logically stronger than the diagonal half.) -/
theorem czCubeLocal_charZeroK2CubeGapPos_of_residue_of_rowPar (h : CZCubeLocalResidueStatement)
    (hrow : ∀ m : ℕ, 0 < m → ∀ k : ℕ, 0 < k →
      Function.Injective
        (vdkRowPar (n := k + 4) (R := MvPolynomial (Fin k) (Localization.Away (m : ℤ))))) :
    CharZeroK2CubeGapPosStatement :=
  czCubeGap_charZeroK2CubeGapPos_of_local_of_rowPar (czCubeLocal_gapLocalOver_of_residue h) hrow

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_charZeroK2CubeGapPos_of_residue_of_rowPar

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
