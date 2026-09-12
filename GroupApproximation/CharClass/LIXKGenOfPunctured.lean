import GroupApproximation.CharClass.LIXKGenPunctured
import GroupApproximation.CharClass.LIXKGenSection
import GroupApproximation.CharClass.ThomProjectivePuncturedOf
import GroupApproximation.CharClass.ThomToolkitInstanceOf
import GroupApproximation.CharClass.KroneckerSphere
import GroupApproximation.Meta.AxiomGuard

/-!
# The punctured-product vanishing over `S¹ × S^{2n+1} × ∏ ℂP^{d_j}`, over a field

Lane `lix-powers` (odd-`p` twins of lane `lix-oddside-n`'s rank-`n` Step C).

`CharClass/LIXKGenPunctured.lean` proves the rank-`n` LIX base top-punctured acyclic at every
point with `F₂` coefficients.  The recursion is coefficient-free: it re-brackets the base with
`KGen.baseNilHomeo` / `KGen.baseSnocHomeo` and peels one `ℂP` factor at a time.  Over a field
`K` every input exists on main: lane `lix-thom`'s `puncturedAcyclic_prodOf`,
`puncturedAcyclic_sphereOf`, `puncturedAcyclic_CPOf`, `kunnethFactor_sphereOf`,
`kunnethFactor_CP_puncturedOf`, `kunnethFactor_sphere_complOf`, and lane `lix-cupone`'s
`sphere_coh_isZero_of_gtOf`.

## Main declarations

* `KGen.hbaseOf K n w` — `S¹ × S^{2n+1}` is top-punctured acyclic in degree `2n + 2`.
* `KGen.puncturedAcyclic_lixBaseOf K n ℓ dd hdd z`.
* `KGen.puncturedAcyclic_lixKZeroOf K n k dd hdd i` — at each of the `k+1` zeros, in degree
  `2 · lixRank n dd`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open CategoryTheory Limits
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-- `H^k(S^{2n+1}; K) = 0` above the dimension, at the ambient `Fin (2n+2)`. -/
theorem isZero_cohomology_sphereOddOf (K : Type) [Field K] (n k : ℕ) (hk : 2 * n + 1 < k) :
    IsZero (Hmod K
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 2))) 1)) k) := by
  have h := sphere_coh_isZero_of_gtOf K (2 * n + 1) k hk
  exact h

/-- The Hermitian sphere `S^{2n+1}` is a Künneth factor of dimension `2n+1`, over `K`. -/
theorem kunnethFactor_unitVectorsOf (K : Type) [Field K] (n : ℕ) :
    KunnethFactorOf K ↥(unitVectors (Fin (n + 1))) (2 * n + 1) := by
  have h : KunnethFactorOf K
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 2))) 1) (2 * n + 1) :=
    kunnethFactor_sphereOf K (2 * n + 1)
  exact KunnethFactorOf.congrHomotopy (unitVectorsHomeo n).toHomotopyEquiv h

/-- Its punctured companion, at any degree, over `K`. -/
theorem kunnethFactor_unitVectors_complOf (K : Type) [Field K] (n : ℕ)
    (y : ↥(unitVectors (Fin (n + 1)))) (q : ℕ) :
    KunnethFactorOf K ↥({y}ᶜ : Set ↥(unitVectors (Fin (n + 1)))) q :=
  KunnethFactorOf.congrHomotopy (homeomorphCompl (unitVectorsHomeo n) y).toHomotopyEquiv
    (kunnethFactor_sphere_complOf K (unitVectorsHomeo n y) q)

/-- **The sphere factor over `K`.** -/
theorem puncturedAcyclic_unitVectorsOf (K : Type) [Field K] (n : ℕ)
    (y : ↥(unitVectors (Fin (n + 1)))) :
    PuncturedAcyclicOf K ↥(unitVectors (Fin (n + 1))) (2 * n + 1) y :=
  PuncturedAcyclicOf.congr' (cohomologyToolkitOf K) (unitVectorsHomeo n) rfl
    (puncturedAcyclic_sphereOf (n := 2 * n + 1) (by omega) (unitVectorsHomeo n y)
      (isZero_cohomology_sphereOddOf K n))

/-- **The circle factor over `K`.** -/
theorem puncturedAcyclic_sphereOneOf (K : Type) [Field K] (w : ↥sphereOne) :
    PuncturedAcyclicOf K ↥sphereOne 1 w :=
  puncturedAcyclic_sphereOf (n := 1) (by omega) w
    (fun k hk => sphere_coh_isZero_of_gtOf K 1 k hk)

/-- **The base case over `K`.**  `S¹ × S^{2n+1}` is top-punctured acyclic in degree `2n + 2`. -/
theorem hbaseOf (K : Type) [Field K] (n : ℕ)
    (w : ↥sphereOne × ↥(unitVectors (Fin (n + 1)))) :
    PuncturedAcyclicOf K (↥sphereOne × ↥(unitVectors (Fin (n + 1)))) (2 * n + 2) w := by
  have hprod := puncturedAcyclic_prodOf (x₀ := w.1) (y₀ := w.2)
    (kunnethFactor_unitVectorsOf K n) (kunnethFactor_unitVectors_complOf K n w.2 (2 * n))
    (puncturedAcyclic_sphereOneOf K w.1) (puncturedAcyclic_unitVectorsOf K n w.2)
  have hdeg : 2 * n + 2 = 1 + (2 * n + 1) := by omega
  rw [hdeg]
  exact hprod

/-- **The punctured-product vanishing at the LIX base, at every rank, over `K`.** -/
theorem puncturedAcyclic_lixBaseOf (K : Type) [Field K] (n : ℕ) :
    ∀ (ℓ : ℕ) (dd : Fin ℓ → ℕ), (∀ j, 0 < dd j) →
    ∀ z : ↥sphereOne × Gen.baseM n dd,
      PuncturedAcyclicOf K (↥sphereOne × Gen.baseM n dd)
        (2 * (∑ j, dd j) + (2 * n + 2)) z := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro dd _ z
    have hdeg : 2 * (∑ j : Fin 0, dd j) + (2 * n + 2) = 2 * n + 2 := by simp
    rw [hdeg]
    exact PuncturedAcyclicOf.congr' (cohomologyToolkitOf K) (baseNilHomeo n dd) rfl
      (hbaseOf K n (baseNilHomeo n dd z))
  | succ ℓ ih =>
    intro dd hdd z
    have hdeg : 2 * (∑ j : Fin (ℓ + 1), dd j) + (2 * n + 2)
        = (2 * (∑ j : Fin ℓ, dd j.castSucc) + (2 * n + 2)) + 2 * dd (Fin.last ℓ) := by
      rw [Fin.sum_univ_castSucc dd]
      ring
    rw [hdeg]
    refine PuncturedAcyclicOf.congr' (cohomologyToolkitOf K) (baseSnocHomeo n dd) rfl ?_
    have hprod := puncturedAcyclic_prodOf
      (x₀ := (baseSnocHomeo n dd z).1) (y₀ := (baseSnocHomeo n dd z).2)
      (kunnethFactor_CPOf K (dd (Fin.last ℓ)))
      (kunnethFactor_CP_puncturedOf K (dd (Fin.last ℓ)) (hdd (Fin.last ℓ))
        (baseSnocHomeo n dd z).2)
      (ih (fun j => dd j.castSucc) (fun j => hdd j.castSucc) (baseSnocHomeo n dd z).1)
      (puncturedAcyclic_CPOf K (dd (Fin.last ℓ)) (hdd (Fin.last ℓ)) (baseSnocHomeo n dd z).2)
    simpa using hprod

/-- **The rank-`n` LIX base is top-punctured acyclic at each of the `k+1` zeros, over `K`.** -/
theorem puncturedAcyclic_lixKZeroOf (K : Type) [Field K] (n k : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (hdd : ∀ j, 0 < dd j) (i : Fin (k + 1)) :
    PuncturedAcyclicOf K (↥sphereOne × Gen.baseM n dd) (2 * lixRank n dd)
      (lixKZero n k dd i) := by
  have h := puncturedAcyclic_lixBaseOf K n ℓ dd hdd (lixKZero n k dd i)
  rwa [show 2 * (∑ j, dd j) + (2 * n + 2) = 2 * lixRank n dd by rw [lixRank]; ring] at h

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.hbaseOf
#audit_axioms KGen.puncturedAcyclic_lixKZeroOf

end GroupApproximation.CharClass
